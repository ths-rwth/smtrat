#pragma once

#include <smtrat-common/model.h>
#include <smtrat-common/settings/Settings.h>
#include <smtrat-common/settings/SettingsParser.h>
#include <smtrat-common/settings/SettingsComponents.h>


#include "../common.h"
#include <smtrat-cad/projectionoperator/utils.h>

namespace smtrat::cad {

struct CADPreprocessorSettings {
	bool disable_variable_elimination = false;
	bool disable_resultants = false;

	static void register_settings(SettingsParser& parser) {
		auto& settings = settings::Settings::getInstance();
		auto& s = settings.get<CADPreprocessorSettings>("cad-pp");
		
		parser.add("CAD Preprocessor settings").add_options()
			("cad.pp.no-elimination", po::bool_switch(&s.disable_variable_elimination), "disable variable elimination")
			("cad.pp.no-resultants", po::bool_switch(&s.disable_resultants), "disable resultant rule")
		;
	}
	static bool register_hook() {
		SettingsComponents::getInstance().add(&register_settings);
		return true;
	}
	static const bool dummy;
};

inline const auto& settings_cadpp() {
	static const auto& s = settings::Settings::getInstance().get<CADPreprocessorSettings>("cad-pp");
	return s;
}

namespace preprocessor {

struct Origins {
	std::map<FormulaT, std::vector<std::vector<FormulaT>>> mOrigins;

	void cleanOrigins(const FormulaT& f);
	void add(const FormulaT& f, const std::vector<FormulaT>& origin);
	void remove(const FormulaT& f);
	const std::vector<FormulaT>& get(const FormulaT& f) const;
	bool resolve(std::set<FormulaT>& conflict) const;
};

class AssignmentCollector {
public:
	/// Result of an assignment collection.
	/// true: new assignments were found
	/// false: no new assignments were found
	/// constraint: found direct conflict
	using CollectionResult = std::variant<bool,ConstraintT>;
private:
	Model& mModel;
	/// Reasons for the assignment of variables.
	std::map<carl::Variable, ConstraintT> mReasons;
	std::map<ConstraintT, carl::Variable> mConstraints;

	bool extractValueAssignments(std::map<ConstraintT, ConstraintT>& constraints);
	bool extractParametricAssignments(std::map<ConstraintT, ConstraintT>& constraints);
	bool extractAssignments(std::map<ConstraintT, ConstraintT>& constraints);
	std::optional<ConstraintT> simplify(std::map<ConstraintT, ConstraintT>& constraints);
public:

	AssignmentCollector(Model& model): mModel(model) {}

	const auto& reasons() const {
		return mReasons;
	}
	auto& reasons() {
		return mReasons;
	}
	const auto& constraints() const {
		return mConstraints;
	}
	auto& constraints() {
		return mConstraints;
	}

	CollectionResult collect(std::map<ConstraintT, ConstraintT>& constraints);
};

class ResultantRule {
private:
	const std::vector<carl::Variable>& mVars;
	std::vector<ConstraintT> mConstraints;
	std::vector<std::vector<UPoly>> mData;
	std::vector<ConstraintT> mNewECs;
	Origins& mOrigins;

	bool addPoly(const Poly& poly);
	bool addPoly(const UPoly& poly, std::size_t level, const std::vector<FormulaT>& origin);
	std::optional<std::vector<FormulaT>> computeResultants(std::size_t level);

public:
	ResultantRule(Origins& origins, const std::vector<carl::Variable>& vars):
		mVars(vars),
		mOrigins(origins)
	{}
	
	std::optional<std::vector<FormulaT>> compute(const std::map<ConstraintT,ConstraintT>& constraints);

	const auto& getNewECs() const {
		return mNewECs;
	}
};

struct ConstraintUpdate {
	std::vector<ConstraintT> toAdd;
	std::vector<ConstraintT> toRemove;
};

}

class CADPreprocessor {
public:
	friend std::ostream& operator<<(std::ostream& os, const CADPreprocessor& cadpp);
private:
	/// The model used for variable elimination.
	Model mModel;
	/// Variable ordering.
	const std::vector<carl::Variable>& mVars;
	/// Origins of new formulas.
	preprocessor::Origins mOrigins;
	/// The assignment collector.
	preprocessor::AssignmentCollector mAssignments;
	/// The resultant rule.
	preprocessor::ResultantRule mResultants;

	/// Equalities from the input.
	std::vector<ConstraintT> mEqualities;
	/// Inequalities from the input.
	std::map<ConstraintT, ConstraintT> mInequalities;
	/// Derived set of equalities, essentially mEqualities - mModel.
	std::map<ConstraintT, ConstraintT> mDerivedEqualities;


	std::optional<std::set<FormulaT>> mConflict;

	void resetCached();
	void removeEquality(const ConstraintT& c);
	bool addEqualities(const std::vector<ConstraintT>& constraints);
	std::vector<ConstraintT> collectDerivedEqualities() const;

	/**
	 * Replace constraints that have been modified by its origins in the given conflict.
	 */
	bool collectOriginsOfConflict(std::set<FormulaT>& conflict, const std::map<ConstraintT, ConstraintT>& constraints) const;
	bool addModelToConflict(std::set<FormulaT>& conflict, carl::Variables& added) const;

public:
	CADPreprocessor(const std::vector<carl::Variable>& vars):
		mModel(),
		mVars(vars),
		mAssignments(mModel),
		mResultants(mOrigins, mVars)
	{}

	void addConstraint(const ConstraintT& c);
	void removeConstraint(const ConstraintT& c);

	/**
	 * Performs the preprocessing.
	 * Return false if a direct conflict was found, true otherwise.
	 */
	bool preprocess();

	const Model& model() const {
		return mModel;
	}

	template<typename Map>
	preprocessor::ConstraintUpdate result(const Map& oldC) const {
		std::set<ConstraintT> newC;
		for (const auto& c: mInequalities) {
			if (c.second.isConsistent() == 1) continue;
			newC.insert(c.second);
		}
		for (const auto& c: mDerivedEqualities) {
			if (c.second.isConsistent() == 1) continue;
			newC.insert(c.second);
		}

		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Old state:" << std::endl << oldC);
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "New state:" << std::endl << newC);

		std::vector<ConstraintT> toAdd;
		std::vector<ConstraintT> toRemove;

		for (const auto& c: newC) {
			if (oldC.find(c) == oldC.end()) toAdd.emplace_back(c);
		}
		for (const auto& c: oldC) {
			if (newC.find(c.first) == newC.end()) toRemove.emplace_back(c.first);
		}

		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "To add:" << std::endl << toAdd);
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "To remove:" << std::endl << toRemove);

		return {toAdd, toRemove};
	}

	std::set<FormulaT> getConflict() const;
	void postprocessConflict(std::set<FormulaT>& mis) const;

	FormulaT simplify(const FormulaT& f) const {
		return carl::model::substitute(f, mModel);
	}
};

inline std::ostream& operator<<(std::ostream& os, const CADPreprocessor& cadpp) {
	os << "Equalities: " << cadpp.mEqualities << std::endl;
	os << "Inequalities: " << cadpp.mInequalities << std::endl;
	os << "Derived: " << cadpp.mDerivedEqualities << std::endl;
	os << "Model: " << cadpp.mModel << std::endl;
	os << "Reasons: " << cadpp.mAssignments.reasons() << std::endl;
	return os;
}



}