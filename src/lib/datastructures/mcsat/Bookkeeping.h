#pragma once

#include "../../Common.h"

namespace smtrat {
namespace mcsat {

/**
 * This class handles all the bookkeeping necessary for all MCSAT backends.
 */
class Bookkeeping {
	/// The current (partial) model.
	Model mModel;
	/// The stack of variables being assigned.
	std::vector<carl::Variable> mAssignedVariables;
	/// The stack of theory assignments.
	std::vector<FormulaT> mAssignments;
	/// The stack of asserted constraints.
	std::vector<FormulaT> mConstraints;
	/// The stack of asserted multivariate root bounds.
	std::vector<FormulaT> mMVBounds;
public:
	
	const auto& model() const {
		return mModel;
	}
	const auto& assignedVariables() const {
		return mAssignedVariables;
	}
	const auto& assignments() const {
		return mAssignments;
	}
	const auto& constraints() const {
		return mConstraints;
	}
	const auto& mvBounds() const {
		return mMVBounds;
	}
	
	
	void pushConstraint(const FormulaT& f) {
		SMTRAT_LOG_TRACE("smtrat.nlsat", "Adding " << f);
		switch (f.getType()) {
			case carl::FormulaType::CONSTRAINT:
				mConstraints.emplace_back(f);
				break;
			case carl::FormulaType::VARCOMPARE:
				mMVBounds.emplace_back(f);
				break;
			default:
				SMTRAT_LOG_ERROR("smtrat.nlsat", "Invalid formula type for a constraint: " << f);
				assert(false);
		}
	}
	
	void popConstraint(const FormulaT& f) {
		SMTRAT_LOG_TRACE("smtrat.nlsat", "Removing " << f);
		switch (f.getType()) {
			case carl::FormulaType::CONSTRAINT:
				assert(mConstraints.back() == f);
				mConstraints.pop_back();
				break;
			case carl::FormulaType::VARCOMPARE:
				assert(mMVBounds.back() == f);
				mMVBounds.pop_back();
				break;
			default:
				SMTRAT_LOG_ERROR("smtrat.nlsat", "Invalid formula type for a constraint: " << f);
				assert(false);
		}
	}
	
	void pushAssignment(carl::Variable v, const ModelValue& mv, const FormulaT& f) {
		SMTRAT_LOG_TRACE("smtrat.nlsat", "Adding " << v << " = " << mv);
		assert(mModel.find(v) == mModel.end());
		mModel.emplace(v, mv);
		mAssignedVariables.emplace_back(v);
		mAssignments.emplace_back(f);
	}

	void popAssignment(carl::Variable v) {
		SMTRAT_LOG_TRACE("smtrat.nlsat", "Removing " << v << " = " << mModel.evaluated(v));
		assert(!mAssignedVariables.empty() && mAssignedVariables.back() == v);
		mModel.erase(v);
		mAssignedVariables.pop_back();
		mAssignments.pop_back();
	}
};

inline std::ostream& operator<<(std::ostream& os, const Bookkeeping& bk) {
	os << "MCSAT:" << std::endl;
	os << "## Model: " << bk.model() << std::endl;
	os << "## Assigned Vars: " << bk.assignedVariables() << std::endl;
	os << "## Assignments: " << bk.assignments() << std::endl;
	os << "## Constraints: " << bk.constraints() << std::endl;
	os << "## Bounds: " << bk.mvBounds() << std::endl;
	return os;
}

}
}
