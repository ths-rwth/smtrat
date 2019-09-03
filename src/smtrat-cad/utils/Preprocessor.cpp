#include "Preprocessor.h"

#include <smtrat-cad/projectionoperator/utils.h>

#include <algorithm>

namespace smtrat::cad {

void Preprocessor::apply_assignments(const ConstraintT& c) {
	ConstraintT cur = c;
	assert(mCurrent.find(cur) != mCurrent.end());
	Model m;
	std::vector<ConstraintT> toAdd;
	for (std::size_t tid = 0; tid < mTrailID; ++tid) {
		auto it = mAssignments.find(mTrail[tid].first);
		if (it != mAssignments.end()) {
			m.emplace(it->second, mModel.at(it->second));
			auto tmp = carl::model::substitute(cur, m);
			if (tmp != cur) {
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Simplifying " << cur << " -> " << tmp << " with " << *it);
				if (tmp.isConsistent() != 1) {
					toAdd.emplace_back(tmp);
				}
				Origins o({cur, it->first});
				std::sort(o.begin(), o.end());
				mTrail.emplace_back(tmp, o);
				mCurrent.erase(cur);
				cur = tmp;
			};
		}
	}
	mCurrent.insert(toAdd.begin(), toAdd.end());
}

void Preprocessor::resolve_conflict() {
	assert(mTrail[mTrailID].first.isConsistent() == 0);
	mConflict = std::set<FormulaT>();
	mConflict->insert(mTrail[mTrailID].second.begin(), mTrail[mTrailID].second.end());
	postprocessConflict(*mConflict);
}

carl::Variable Preprocessor::main_variable_of(const ConstraintT& c) const {
	carl::carlVariables vars;
	c.gatherVariables(vars);
	for (auto v: mVars) {
		if (vars.has(v)) return v;
	}
	return carl::Variable::NO_VARIABLE;
}

bool Preprocessor::try_variable_elimination(const ConstraintT& cur) {
	carl::Variable v;
	Rational r;
	Poly p;
	bool foundAssignment = false;
	if (cur.getAssignment(v, r)) {
		auto mit = mModel.find(v);
		if (mit != mModel.end()) {
			assert(mModel.at(v).isRational() && mModel.at(v).asRational() == r);
			return false;
		}
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Newly extracted " << v << " = " << r);
		mModel.emplace(v, r);
		mAssignments.emplace(cur, v);
		foundAssignment = true;
	} else if (cur.getSubstitution(v, p)) {
		auto mit = mModel.find(v);
		if (mit != mModel.end()) {
			return false;
		}
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Newly extracted " << v << " = " << p);
		mModel.emplace(v, carl::createSubstitution<Rational,Poly,ModelPolynomialSubstitution>(p));
		mAssignments.emplace(cur, v);
		foundAssignment = true;
	}
	if (foundAssignment) {
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Simplifying with new assignment");
		std::vector<ConstraintT> toAdd;
		for (auto it = mCurrent.begin(); it != mCurrent.end();) {
			if (*it == cur) {
				it = mCurrent.erase(it);
				continue;
			}
			auto tmp = carl::model::substitute(*it, mModel);
			if (tmp != *it) {
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Simplifying " << *it << " -> " << tmp);
				if (mCurrent.find(tmp) == mCurrent.end()) {
					if (tmp.isConsistent() != 1) {
						toAdd.emplace_back(tmp);
					}
					Origins o({cur, *it});
					std::sort(o.begin(), o.end());
					mTrail.emplace_back(tmp, o);
				}
				it = mCurrent.erase(it);
			} else ++it;
		}
		mCurrent.insert(toAdd.begin(), toAdd.end());
		return true;
	}
	return false;
}

void Preprocessor::compute_resultants(const ConstraintT& cur) {
	carl::Variable mainvar = main_variable_of(cur);
	if (mainvar == carl::Variable::NO_VARIABLE) return;
	auto p = cur.lhs().toUnivariatePolynomial(mainvar);
	SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Identified main variable of " << p << ": " << mainvar);
	std::vector<ConstraintT> toAdd;
	for (const auto& c: mCurrent) {
		if (mainvar == main_variable_of(c)) {
			auto q = c.lhs().toUnivariatePolynomial(mainvar);
			auto r = projection::resultant(mainvar, p, q);
			if (!r.isNumber()) {
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Resultant of " << p << " and " << q << " is " << r);
				toAdd.emplace_back(Poly(r), carl::Relation::EQ);
				Origins o({cur, c});
				std::sort(o.begin(), o.end());
				mTrail.emplace_back(toAdd.back(), o);
			}
		}
	}
	mCurrent.insert(toAdd.begin(), toAdd.end());
}

void Preprocessor::addConstraint(const ConstraintT& c) {
	SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Adding " << c << " to" << std::endl << *this);
	mCurrent.emplace(c);
	mTrail.emplace_back(c, Origins());
	SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Reapplying assignments to " << c << " in" << std::endl << *this);
	apply_assignments(c);
}
void Preprocessor::removeConstraint(const ConstraintT& c) {
	SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Removing " << c << " from" << std::endl << *this);
	std::vector<ConstraintT> removals({c});
	for (const auto& t: mTrail) {
		for (const auto& r: removals) {
			auto it = std::lower_bound(t.second.begin(), t.second.end(), r);
			if (it != t.second.end() && *it == r) {
				removals.emplace_back(t.first);
				break;
			}
		}
	}
	SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Going to remove " << removals);
	SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Model is now " << mModel);
	for (const auto& r: removals) {
		auto ait = mAssignments.find(r);
		if (ait != mAssignments.end()) {
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Purging " << ait->second << " from model due to " << r);
			mModel.erase(ait->second);
			mAssignments.erase(ait);
		}
	}
	SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Model is now " << mModel);
	SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Cleaning " << mCurrent);
	for (std::size_t curID = mTrail.size(); curID > 0; --curID) {
		const auto& cur = mTrail[curID - 1];
		if (std::find(removals.begin(), removals.end(), cur.first) == removals.end()) {
			continue;
		}
		auto it = mCurrent.find(cur.first);
		if (it != mCurrent.end()) {
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Replace " << cur.first << " by " << cur.second);
			mCurrent.erase(it);
			mCurrent.insert(cur.second.begin(), cur.second.end());
		} else if (cur.first.isConsistent() == 1) {
			for (const auto& o: cur.second) {
				auto it = std::find(removals.begin(), removals.end(), o);
				if (it != removals.end()) {
					SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Restoring " << cur.first << " by " << cur.second);
					mCurrent.insert(cur.second.begin(), cur.second.end());
					break;
				}
			}
		}
	}
	SMTRAT_LOG_DEBUG("smtrat.cad.pp", "-> " << mCurrent);

	auto it = std::remove_if(mTrail.begin(), mTrail.end(),
		[&removals](const auto& val){
			return std::find(removals.begin(), removals.end(), val.first) != removals.end();
		}
	);
	mTrail.erase(it, mTrail.end());
	mTrailID = 0;
	mModel.clear();
	SMTRAT_LOG_DEBUG("smtrat.cad.pp", "State after removal" << std::endl << *this);
}

void Preprocessor::postprocessConflict(std::set<FormulaT>& mis) const {
	SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Postprocessing " << mis);
	for (std::size_t curID = mTrail.size(); curID > 0; --curID) {
		const auto& cur = mTrail[curID - 1];
		if (cur.second.size() == 0) {
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Keep " << cur.first << " as original constraint.");
			// This was an original constraint
			continue;
		}
		auto it = mis.find(FormulaT(cur.first));
		if (it != mis.end()) {
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Replace " << cur.first << " by " << cur.second);
			mis.erase(it);
			mis.insert(cur.second.begin(), cur.second.end());
		}
	}
	SMTRAT_LOG_DEBUG("smtrat.cad.pp", "-> " << mis);
}

bool Preprocessor::preprocess() {
	SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Preprocessing from" << std::endl << *this);
	mConflict = std::nullopt;
	while (mTrailID < mTrail.size()) {
		auto cur = mTrail[mTrailID].first;
		if (cur.isConsistent() == 0) {
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Found conflict in " << mTrail[mTrailID]);
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "After preprocessing:" << std::endl << *this);
			resolve_conflict();
			return false;
		}
		auto it = mAssignments.find(cur);
		if (it != mAssignments.end()) {
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Redo variable elimination for " << cur);
			try_variable_elimination(cur);
			++mTrailID;
			continue;
		}
		if (mCurrent.find(cur) == mCurrent.end()) {
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Skip " << cur << " @ " << mTrailID << " as it has already been eliminated.");
			++mTrailID;
			continue;
		}
		if (cur.relation() != carl::Relation::EQ) {
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Skip " << cur << " @ " << mTrailID << " as it is not an equality.");
			++mTrailID;
			continue;
		}
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Continuing with " << mTrail[mTrailID]);
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Current state: " << mCurrent);
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Variable elimination with " << cur);
		if (settings_cadpp().disable_variable_elimination) {
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Variable elimination is disabled");
		} else if (try_variable_elimination(cur)) {
			++mTrailID;
			continue;
		}

		if (settings_cadpp().disable_resultants) {
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Resultant computation is disabled");
		} else {
			compute_resultants(cur);
		}
		++mTrailID;
	
	}
	SMTRAT_LOG_DEBUG("smtrat.cad.pp", "After preprocessing:" << std::endl << *this);
	return true;
}

} // namespace smtrat::cad
