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
	CAD& mCAD;
	std::map<ConstraintT, boost::optional<ConstraintT>> mConstraints;
	std::set<ConstraintT> mForwardedConstraints;
	std::map<carl::Variable, ConstraintT> mAssignments;
	Model mModel;
	boost::optional<ConstraintT> mConflict;
public:
	EqualityReplacer(CAD& cad): mCAD(cad) {}
	void addConstraint(const ConstraintT& c) {
		SMTRAT_LOG_DEBUG("smtrat.cad", "Adding " << c);
		mConstraints.emplace(c, boost::none);
	}
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
	void addAssignment(carl::Variable v, const ModelValue& n, const ConstraintT& c) {
		mModel.emplace(v, n);
		mAssignments.emplace(v, c);
	}
	void removeAssignment(carl::Variable v) {
		auto it = mModel.find(v);
		assert(it != mModel.end());
		mModel.erase(it);
		auto ait = mAssignments.find(v);
		assert(ait != mAssignments.end());
		SMTRAT_LOG_DEBUG("smtrat.cad", "Removing assignment " << ait->second);
		mCAD.removeConstraint(ait->second);
		mAssignments.erase(ait);
	}
	bool commit() {
		SMTRAT_LOG_INFO("smtrat.cad", "Using " << mModel << " to simplify");
		for (auto& c: mConstraints) {
			auto res = carl::model::substitute(c.first, mModel);
			if (c.second) {
				assert(c.second != boost::none);
				if (res == c.second) continue;
				SMTRAT_LOG_DEBUG("smtrat.cad", "Actually Erasing " << *c.second);
				mCAD.removeConstraint(*c.second);
				mForwardedConstraints.erase(*c.second);
			}
			if (mForwardedConstraints.find(res) != mForwardedConstraints.end()) {
				c.second = boost::none;
				continue;
			}
			SMTRAT_LOG_INFO("smtrat.cad", c.first << " -> " << res);
			if (res.isConsistent() == 0) {
				mConflict = c.first;
				return false;
			}
			if (res.isConsistent() == 2) {
				c.second = res;
				SMTRAT_LOG_DEBUG("smtrat.cad", "Actually Adding " << *c.second);
				mCAD.addConstraint(*c.second);
				mForwardedConstraints.insert(*c.second);
			}
		}
		for (const auto& ass: mAssignments) {
			if (mForwardedConstraints.find(ass.second) != mForwardedConstraints.end()) continue;
			SMTRAT_LOG_DEBUG("smtrat.cad", "Adding Assignment " << ass.second);
			mCAD.addConstraint(ass.second);
			mForwardedConstraints.insert(ass.second);
		}
		return true;
	}
	void buildInfeasibleSubset(FormulaSetT& mis) const {
		mis.insert(FormulaT(*mConflict));
		for (const auto& ass: mAssignments) {
			mis.insert(FormulaT(ass.second));
		}
	}
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
