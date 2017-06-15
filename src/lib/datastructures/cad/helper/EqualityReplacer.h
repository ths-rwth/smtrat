#pragma once

#include "../Common.h"

#include <carl/formula/model/evaluation/ModelEvaluation.h>

#include <boost/optional.hpp>

#include <map>

namespace smtrat {
namespace cad {

template<typename CAD>
class EqualityReplacer {
public:
	using RAN = carl::RealAlgebraicNumber<smtrat::Rational>;
private:
	/// CAD that is used as backend.
	CAD& mCAD;
	/// Maps input constraints to simplified ones.
	std::map<ConstraintT, boost::optional<ConstraintT>> mConstraints;
	/// Set of constraints that are currently forwarded to mCAD.
	std::set<ConstraintT> mForwardedConstraints;
	/// Current assignment that is used for simplication.
	std::map<carl::Variable, ConstraintT> mAssignments;
	/// Assignments to variables already assigned.
	std::map<ConstraintT, std::pair<carl::Variable, ModelValue>> mDuplicateAssignments;
	/// Current model that matches mAssignments.
	Model mModel;
	/// A constraint that is trivially false under the current model.
	boost::optional<ConstraintT> mConflict;
public:
	EqualityReplacer(CAD& cad): mCAD(cad) {}
	/**
	 * Adds a constraint.
	 *
	 * It is forwarded with the next call to commit().
	 */
	void addConstraint(const ConstraintT& c) {
		SMTRAT_LOG_DEBUG("smtrat.cad", "Adding " << c);
		mConstraints.emplace(c, boost::none);
	}
	/**
	 * Removes a constraint.
	 *
	 * If it has already been forwarded, it is removed immediately.
	 */
	void removeConstraint(const ConstraintT& c) {
		SMTRAT_LOG_DEBUG("smtrat.cad", "Removing " << c);
		auto it = mConstraints.find(c);
		assert(it != mConstraints.end());
		if (it->second) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Actually Erasing " << *it->second);
			mCAD.removeConstraint(*it->second);
			mForwardedConstraints.erase(*it->second);
		}
		mConstraints.erase(it);
	}
	/**
	 * Adds an assignment.
	 *
	 * It is used for simplication in the next call to commit().
	 */
	void addAssignment(carl::Variable v, const ModelValue& n, const ConstraintT& c) {
		SMTRAT_LOG_DEBUG("smtrat.cad", "Adding " << c);
		auto it = mAssignments.find(v);
		if (it == mAssignments.end()) {
			mModel.emplace(v, n);
			mAssignments.emplace(v, c);
		} else {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Is duplicate " << c);
			mDuplicateAssignments.emplace(c, std::make_pair(v, n));
		}
	}
	/**
	 * Removes an assignment.
	 *
	 * Simplified constraints are updated in the next call to commit().
	 */
	void removeAssignment(carl::Variable v, const ConstraintT& c) {
		SMTRAT_LOG_DEBUG("smtrat.cad", "Removing assignment for " << v);
		auto dait = mDuplicateAssignments.find(c);
		if (dait != mDuplicateAssignments.end()) {
			mDuplicateAssignments.erase(dait);
		} else {
			auto it = mModel.find(v);
			if (it == mModel.end()) std::exit(55);
			assert(it != mModel.end());
			mModel.erase(it);
			auto ait = mAssignments.find(v);
			assert(ait != mAssignments.end());
			SMTRAT_LOG_DEBUG("smtrat.cad", "Removing assignment " << ait->second);
			mCAD.removeConstraint(ait->second);
			mForwardedConstraints.erase(ait->second);
			mAssignments.erase(ait);
		}
	}
	/**
	 * Actually commits new constraints and simplications to CAD.
	 */
	bool commit() {
		SMTRAT_LOG_DEBUG("smtrat.cad", "Commit ");
		for (auto it = mDuplicateAssignments.begin(); it != mDuplicateAssignments.end();) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Looking at duplicate " << it->first);
			if (mAssignments.find(it->second.first) == mAssignments.end()) {
				SMTRAT_LOG_DEBUG("smtrat.cad", "Duplicate is now first one, adding assignment");
				addAssignment(it->second.first, it->second.second, it->first);
				it = mDuplicateAssignments.erase(it);
			} else {
				SMTRAT_LOG_DEBUG("smtrat.cad", "Model: " << mModel);
				auto res = carl::model::evaluate(it->first, mModel);
				SMTRAT_LOG_DEBUG("smtrat.cad", "Evaluated to " << res);
				assert(res.isBool());
				if (!res.asBool()) {
					SMTRAT_LOG_DEBUG("smtrat.cad", "Duplicate constraint is a conflict: " << it->first);
					mConflict = it->first;
					return false;
				} else {
					SMTRAT_LOG_DEBUG("smtrat.cad", "Evaluated to true:" << res);
				}
				it++;
			}
		}
		SMTRAT_LOG_INFO("smtrat.cad", "Using " << mModel << " to simplify");
		for (auto& c: mConstraints) {
			auto res = carl::model::substitute(c.first, mModel);
			if (c.second) {
				// Constraint has already been simplified
				assert(c.second != boost::none);
				if (res == c.second) continue;
				// Old simplication is invalid, remove it.
				SMTRAT_LOG_DEBUG("smtrat.cad", "Actually Erasing " << *c.second);
				mCAD.removeConstraint(*c.second);
				mForwardedConstraints.erase(*c.second);
				c.second = boost::none;
			}
			if (mForwardedConstraints.find(res) != mForwardedConstraints.end()) {
				// The (simplified?) constraint has already been forwarded.
				SMTRAT_LOG_DEBUG("smtrat.cad", "Not considering " << res);
				continue;
			}
			SMTRAT_LOG_INFO("smtrat.cad", c.first << " -> " << res);
			if (res.isConsistent() == 0) {
				// The constraint is trivially false under the model.
				mConflict = c.first;
				return false;
			}
			if (res.isConsistent() == 2) {
				// The constraint is forwarded to the CAD.
				c.second = res;
				SMTRAT_LOG_DEBUG("smtrat.cad", "Actually Adding " << *c.second);
				mCAD.addConstraint(*c.second);
				mForwardedConstraints.insert(*c.second);
			}
		}
		for (const auto& ass: mAssignments) {
			// Forward the assignment to the CAD.
			if (mForwardedConstraints.find(ass.second) != mForwardedConstraints.end()) continue;
			SMTRAT_LOG_DEBUG("smtrat.cad", "Adding Assignment " << ass.second);
			mCAD.addConstraint(ass.second);
			mForwardedConstraints.insert(ass.second);
		}
		return true;
	}
	/**
	 * Builds a trivial infeasible subset from a conflicting constraint and the current assignment.
	 */
	void buildInfeasibleSubset(FormulaSetT& mis) const {
		mis.insert(FormulaT(*mConflict));
		for (const auto& ass: mAssignments) {
			mis.insert(FormulaT(ass.second));
		}
	}
	/**
	 * Replaces all simplified constraints by their original version.
	 */
	void preprocessInfeasibleSubset(FormulaSetT& mis) const {
		for (const auto& cons: mConstraints) {
			if (cons.second) {
				auto it = mis.find(FormulaT(*cons.second));
				if (it == mis.end()) continue;
				mis.erase(it);
				mis.emplace(cons.first);
			}
		}
	}
};

}
}
