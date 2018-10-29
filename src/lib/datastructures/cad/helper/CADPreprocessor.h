#pragma once

#include "../Common.h"

namespace smtrat::cad {

namespace preprocessor {

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

	bool extractValueAssignments(std::map<ConstraintT, ConstraintT>& constraints) {
		carl::Variable v;
		Rational r;
		bool foundAssignment = false;
		for (auto it = constraints.begin(); it != constraints.end(); ) {
			if (it->second.getAssignment(v, r) && mModel.find(v) == mModel.end()) {
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Newly extracted " << v << " = " << r);
				mModel.emplace(v, r);
				mReasons.emplace(v, it->first);
				it = constraints.erase(it);
				foundAssignment = true;
			} else {
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "No assignment from " << it->second);
				++it;
			}
		}
		return foundAssignment;
	}
	bool extractParametricAssignments(std::map<ConstraintT, ConstraintT>& constraints) {
		carl::Variable v;
		Poly r;
		bool foundAssignment = false;
		for (auto it = constraints.begin(); it != constraints.end(); ) {
			if (it->second.getSubstitution(v, r) && mModel.find(v) == mModel.end()) {
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Newly extracted " << v << " = " << r);
				mModel.emplace(v, carl::createSubstitution<Rational,Poly,ModelPolynomialSubstitution>(r));
				mReasons.emplace(v, it->first);
				it = constraints.erase(it);
				foundAssignment = true;
			} else {
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "No assignment from " << it->second);
				++it;
			}
		}
		return foundAssignment;
	}

	bool extractAssignments(std::map<ConstraintT, ConstraintT>& constraints) {
		if (extractValueAssignments(constraints)) return true;
		return extractParametricAssignments(constraints);
	}

	std::optional<ConstraintT> simplify(std::map<ConstraintT, ConstraintT>& constraints) {
		for (auto& c: constraints) {
			carl::model::substituteIn(c.second, mModel);
			if (c.second.isConsistent() == 0) {
				return c.first;
			}
		}
		return std::nullopt;
	}
public:

	AssignmentCollector(Model& model): mModel(model) {}

	const auto& reasons() const {
		return mReasons;
	}

	CollectionResult collect(std::map<ConstraintT, ConstraintT>& constraints) {
		bool foundAssignments = extractAssignments(constraints);
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Extracted assignments " << mModel << " from " << constraints);
		if (auto c = simplify(constraints); c) {
			return *c;
		}
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "After simplication with " << mModel << ": " << constraints);
		if (!foundAssignments) return false;
		while (foundAssignments) {
			foundAssignments = extractAssignments(constraints);
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Extracted assignments " << mModel << " from " << constraints);
			if (auto c = simplify(constraints); c) {
				return *c;
			}
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "After simplication with " << mModel << ": " << constraints);
		}
		return true;
	}
};

class ResultantRule {
private:
	const std::vector<carl::Variable>& mVars;
	std::vector<std::vector<UPoly>> mData;
	std::vector<ConstraintT> mNewECs;

	void addPoly(const Poly& poly) {
		if (poly.isNumber()) return;
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Adding poly " << poly << " under ordering " << mVars);
		std::size_t level = 0;
		UPoly p = poly.toUnivariatePolynomial(mVars[level]);
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "-> " << p);
		while (p.isConstant()) {
			++level;
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", p << " is constant, moving to level " << level);
			p = poly.toUnivariatePolynomial(mVars[level]);
		}
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Inserting " << p << " into level " << level);
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Into " << mData);
		mData[level].emplace_back(p);
	}

	void addPoly(const UPoly& poly, std::size_t level = 0) {
		if (poly.isNumber()) return;
		Poly mp(poly);
		UPoly p = poly;
		assert(p.mainVar() == mVars[level]);
		while (p.isConstant()) {
			++level;
			p = mp.toUnivariatePolynomial(mVars[level]);
		}
		mData[level].emplace_back(p);
		mNewECs.emplace_back(mp, carl::Relation::EQ);
	}

	void computeResultants(std::size_t level) {
		for (std::size_t pid = 0; pid < mData[level].size(); ++pid) {
			for (std::size_t qid = pid + 1; qid < mData[level].size(); ++qid) {
				addPoly(projection::resultant(mVars[level + 1], mData[level][pid], mData[level][qid]), level + 1);
			}
		}
	}

	void computeResultants() {
		for (std::size_t level = 0; level < mData.size() - 1; ++level) {
			computeResultants(level);
		}
	}
public:
	ResultantRule(const std::vector<carl::Variable>& vars):
		mVars(vars)
	{}
	
	std::vector<ConstraintT> complete(const std::vector<ConstraintT>& constraints) {
		mData.assign(mVars.size(), {});
		for (const auto& c: constraints) {
			addPoly(c.lhs());
		}
		computeResultants();
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

	std::optional<ConstraintT> mConflict;

	void removeEquality(const ConstraintT& c) {
		mDerivedEqualities.clear();
		std::remove(mEqualities.begin(), mEqualities.end(), c);
		for (auto& i: mInequalities) {
			i.second = i.first;
		}
	}

	bool addEqualities(const std::vector<ConstraintT>& constraints) {
		bool addedNew = false;
		for (const auto& c: constraints) {
			if (mDerivedEqualities.try_emplace(c, c).second) {
				addedNew = true;
			}
		}
		return addedNew;
	}

	std::vector<ConstraintT> collectDerivedEqualities() const {
		std::vector<ConstraintT> cur;
		for (const auto& c: mDerivedEqualities) {
			cur.emplace_back(c.second);
		}
		return cur;
	}

	/**
	 * Replace constraints that have been modified by its origins in the given conflict.
	 */
	void collectOriginsOfConflict(std::set<FormulaT>& conflict, const std::map<ConstraintT, ConstraintT>& constraints) const {
		for (const auto& c: constraints) {
			if (c.first == c.second) continue;
			if (conflict.erase(FormulaT(c.second)) > 0) {
				conflict.emplace(c.first);
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Replaced " << c.second << " by origin " << c.first);
			}
		}
	}

public:
	CADPreprocessor(const std::vector<carl::Variable>& vars):
		mModel(),
		mVars(vars),
		mAssignments(mModel),
		mResultants(mVars)
	{}

	void addConstraint(const ConstraintT& c) {
		if (c.relation() == carl::Relation::EQ) {
			mEqualities.emplace_back(c);
		} else {
			mInequalities.emplace(c, c);
		}
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Added " << c << " to " << std::endl << *this);
	}

	void removeConstraint(const ConstraintT& c) {
		if (c.relation() == carl::Relation::EQ) {
			removeEquality(c);
		} else {
			auto it = mInequalities.find(c);
			assert(it != mInequalities.end());
			mInequalities.erase(it);
		}
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Removed " << c << " from " << std::endl << *this);
	}

	/**
	 * Performs the preprocessing.
	 * Return false if a direct conflict was found, true otherwise.
	 */
	bool preprocess() {
		std::vector<ConstraintT> cur = mEqualities;
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Starting with:" << std::endl << *this);
		while (addEqualities(cur)) {
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Collecting assignments from:" << std::endl << *this);
			auto collectResult = mAssignments.collect(mDerivedEqualities);
			if (std::holds_alternative<ConstraintT>(collectResult)) {
				mConflict = std::get<ConstraintT>(collectResult);
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Immediate conflict due to " << *mConflict);
				return false;
			}
			assert(std::holds_alternative<bool>(collectResult));
			if (std::get<bool>(collectResult) == false) {
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "No further assignments.");
				break;
			}
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Collected assignments:" << std::endl << *this);
			
			cur = mResultants.complete(collectDerivedEqualities());
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Computed resultants:" << std::endl << *this << std::endl << "-> " << cur);
		}
		for (auto& c: mInequalities) {
			carl::model::substituteIn(c.second, mModel);
			if (c.second.isConsistent() == 0) {
				mConflict = c.first;
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Immediate conflict due to " << *mConflict);
				return false;
			}
		}
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "After preprocessing:" << std::endl << *this);
		return true;
	}

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
			if (newC.find(c.first) == newC.end()) toAdd.emplace_back(c.first);
		}

		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "To add:" << std::endl << toAdd);
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "To remove:" << std::endl << toRemove);

		return {toAdd, toRemove};
	}

	std::set<FormulaT> getConflict() const {
		assert(mConflict);
		std::set<FormulaT> res;
		res.emplace(*mConflict);
		for (auto v: mConflict->variables()) {
			auto it = mAssignments.reasons().find(v);
			if (it != mAssignments.reasons().end()) {
				res.emplace(it->second);
			}
		}
		return res;
	}

	void postprocessConflict(std::set<FormulaT>& mis) const {
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Postprocessing conflict: " << mis << " based on" << std::endl << *this);
		collectOriginsOfConflict(mis, mDerivedEqualities);
		collectOriginsOfConflict(mis, mInequalities);
		carl::Variables vars;
		for (const auto& f: mis) f.allVars(vars);
		for (auto v: vars) {
			auto it = mAssignments.reasons().find(v);
			if (it == mAssignments.reasons().end()) continue;
			mis.emplace(it->second);
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Added " << it->second << " to conflict.");
		}
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Postprocessed conflict: " << mis);
	}
};

inline std::ostream& operator<<(std::ostream& os, const CADPreprocessor& cadpp) {
	os << "Equalities: " << cadpp.mEqualities << std::endl;
	os << "Inequalities: " << cadpp.mInequalities << std::endl;
	os << "Derived: " << cadpp.mDerivedEqualities << std::endl;
	os << "Model: " << cadpp.mModel << std::endl;
	return os;
}



}