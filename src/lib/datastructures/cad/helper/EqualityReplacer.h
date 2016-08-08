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
	Model mModel;
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
	void addAssignment(carl::Variable v, const ModelValue& n) {
		mModel.emplace(v, n);
	}
	void removeAssignment(carl::Variable v) {
		auto it = mModel.find(v);
		assert(it != mModel.end());
		mModel.erase(it);
	}
	void commit() {
		for (auto& c: mConstraints) {
			auto res = carl::model::substitute(c.first, mModel);
			if (c.second) {
				if (res == c.second) continue;
				mCAD.removeConstraint(*c.second);
			}
			c.second = res;
			assert(c.second->isConsistent() != 0);
			if (c.second->isConsistent() == 2) {
				mCAD.addConstraint(*c.second);
			}
		}
	}
};

}
}
