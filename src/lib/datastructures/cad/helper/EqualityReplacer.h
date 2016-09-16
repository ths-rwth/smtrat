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
	std::map<carl::Variable, ConstraintT> mAssignments;
	Model mModel;
	boost::optional<ConstraintT> mConflict;
public:
	EqualityReplacer(CAD& cad): mCAD(cad) {}
	void addConstraint(const ConstraintT& c) {
		mConstraints.emplace(c, boost::none);
	}
	void removeConstraint(const ConstraintT& c) {
		auto it = mConstraints.find(c);
		assert(it != mConstraints.end());
		assert(it->second != boost::none);
		mCAD.removeConstraint(*it->second);
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
		mCAD.removeConstraint(ait->second);
		mAssignments.erase(ait);
	}
	bool commit() {
		SMTRAT_LOG_INFO("smtrat.cad", "Using " << mModel << " to simplify");
		for (auto& c: mConstraints) {
			auto res = carl::model::substitute(c.first, mModel);
			if (c.second) {
				if (res == c.second) continue;
				mCAD.removeConstraint(*c.second);
			}
			c.second = res;
			SMTRAT_LOG_INFO("smtrat.cad", c.first << " -> " << *c.second);
			if (c.second->isConsistent() == 0) {
				mConflict = c.first;
				return false;
			}
			if (c.second->isConsistent() == 2) {
				mCAD.addConstraint(*c.second);
			}
		}
		for (const auto& ass: mAssignments) {
			mCAD.addConstraint(ass.second);
		}
		return true;
	}
	void buildInfeasibleSubset(FormulaSetT& mis) const {
		mis.insert(FormulaT(*mConflict));
		for (const auto& ass: mAssignments) {
			mis.insert(FormulaT(ass.second));
		}
	}
};

}
}
