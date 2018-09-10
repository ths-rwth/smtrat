#pragma once

#include "../../Common.h"

namespace smtrat {
namespace mcsat {

/**
 * Represent the trace, i.e. the assignment/model state, of a MCSAT run in different
 * representations (kept in sync) for a fast access.
 * Most notably, we store literals, i.e. a polynomial (in)equality-atom or its negation,
 * which we assert to be true. Since the negation can be represented by an atom by
 * flipping the (in)equality, it suffices to store only atoms. Here we call atomic formulas
 * over the theory of real arithmetic "constraints".
 */
class Bookkeeping {
	/** Current (partial) model. */
	Model mModel;
	/** Stack of (algebraic) variables being assigned. */
	std::vector<carl::Variable> mAssignedVariables;
	/** Stack of theory assignments, i.e. the values for the variables. */
	std::vector<FormulaT> mAssignments;
	/** Stack of asserted constraints/literals. */
	std::vector<FormulaT> mConstraints;
	/** Stack of asserted multivariate root bounds. */
	std::vector<FormulaT> mMVBounds;
	/** Sequence defining the variable ordering. */
	std::vector<carl::Variable> mVariableOrdering;
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
	const auto& variableOrder() const {
		return mVariableOrdering;
	}

	void updateVariableOrder(const std::vector<carl::Variable> ordering) {
		mVariableOrdering = ordering;
	}
	
	/** Assert a constraint/literal */
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
	os << "MCSAT trace:" << std::endl;
	os << "## Model: " << bk.model() << std::endl;
	os << "## Assigned Vars: " << bk.assignedVariables() << std::endl;
	os << "## Assigned Values: " << bk.assignments() << std::endl;
	os << "## Asserted constr/lits: " << bk.constraints() << std::endl;
	os << "## Bounds: " << bk.mvBounds() << std::endl;
	os << "## Variable ordering: " << bk.variableOrder() << std::endl;
	return os;
}

}
}
