#pragma once

#include <smtrat-common/model.h>
#include <smtrat-common/settings/Settings.h>
#include <smtrat-common/settings/SettingsParser.h>
#include <smtrat-common/settings/SettingsComponents.h>

namespace smtrat::cad {

struct PreprocessorSettings {
	bool disable_variable_elimination = false;
	bool disable_resultants = false;

	static void register_settings(SettingsParser& parser) {
		namespace po = boost::program_options;
		auto& settings = settings::Settings::getInstance();
		auto& s = settings.get<PreprocessorSettings>("cad-pp2");
		
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
	static const auto& s = settings::Settings::getInstance().get<PreprocessorSettings>("cad-pp2");
	return s;
}

namespace preprocessor {
	struct ConstraintUpdate {
		std::vector<ConstraintT> toAdd;
		std::vector<ConstraintT> toRemove;
	};
}

class Preprocessor {
public:
	friend std::ostream& operator<<(std::ostream& os, const Preprocessor& cadpp);
private:
	using Origins = std::vector<ConstraintT>;
	using Trail = std::vector<std::pair<ConstraintT,Origins>>;

	/// Variable ordering.
	const std::vector<carl::Variable>& mVars;
	/// Origins for the assignments.
	std::map<ConstraintT,carl::Variable> mAssignments;
	/// The model used for variable elimination.
	Model mModel;
	/// The trail.
	Trail mTrail;
	/// Next element to be processed.
	std::size_t mTrailID = 0;
	/// Current set of equalities.
	std::set<ConstraintT> mCurrent;
	/// A possibly found conflict.
	std::optional<std::set<FormulaT>> mConflict;

	void apply_assignments(const ConstraintT& c);
	void resolve_conflict();
	carl::Variable main_variable_of(const ConstraintT& c) const;

	bool try_variable_elimination(const ConstraintT& cur);
	void compute_resultants(const ConstraintT& cur);
public:
	Preprocessor(const std::vector<carl::Variable>& vars):
		mVars(vars)
	{}
	void clear() {
		mAssignments.clear();
		mModel.clear();
		mTrail.clear();
		mTrailID = 0;
		mCurrent.clear();
		mConflict = std::nullopt;
	}
	void addConstraint(const ConstraintT& c);
	void removeConstraint(const ConstraintT& c);
	bool preprocess();
	void postprocessConflict(std::set<FormulaT>& mis) const;

	const Model& model() const {
		return mModel;
	}
	const auto& getConflict() const {
		assert(mConflict);
		return *mConflict;
	}
	FormulaT simplify(const FormulaT& f) const {
		return carl::substitute(f, mModel);
	}

	template<typename Map>
	preprocessor::ConstraintUpdate result(const Map& oldC) const {
		std::set<ConstraintT> newC = mCurrent;

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
};

inline std::ostream& operator<<(std::ostream& os, const Preprocessor& cadpp) {
	os << "Current Trail:" << std::endl;
	for (const auto& t: cadpp.mTrail) {
		if (cadpp.mTrailID < cadpp.mTrail.size() && cadpp.mTrail[cadpp.mTrailID] == t) {
			os << "-->";
		}
		os << "\t" << t.first << "\t" << t.second << std::endl;
	}
	os << "Model: " << cadpp.mModel << std::endl;
	os << "from   " << cadpp.mAssignments << std::endl;
	os << "Current: " << cadpp.mCurrent << std::endl;
	return os;
}

}