#pragma once

#include "../../../Common.h"

#include "AssignmentFinder.h"

#include <boost/optional.hpp>

namespace smtrat {
namespace nlsat {

class NLSAT {
public:
	friend std::ostream& operator<<(std::ostream& os, const NLSAT& nl);
private:
	std::vector<FormulaT> mConstraints;
	std::vector<FormulaT> mMVBounds;
	Model mModel;
	std::vector<carl::Variable> mVariables;
	std::vector<FormulaT> mAssignments;
	
	FormulaT resolveNegation(const FormulaT& f) const;
	
public:
	/**
	 * Add a new constraint.
	 */
	void pushConstraint(const FormulaT& f);
	/**
	 * Remove the last constraint. f must be the same as the one passed to the last call of pushConstraint().
	 */
	void popConstraint(const FormulaT& f);
	/**
	 * Add a new assignment.
	 */
	void pushAssignment(carl::Variable v, const ModelValue& mv, const FormulaT& f);
	/**
	 * Remove the last assignment. v must be the same as the one passed to the last call of pushAssignment().
	 */
	void popAssignment(carl::Variable v);
	
	const auto& getModel() const {
		return mModel;
	}
	
	/**
	 * Try to find a consistent assignment for the given variable
	 * Returns a variant containing
	 * - either an assignment (as ModelValue)
	 * - or an conflicting core (as FormulasT)
	 */
	AssignmentFinder::AssignmentOrConflict findAssignment(carl::Variable var) const;
	
	/**
	 * Check whether the given constraint is consistent with the current state
	 * If it is, returns boost::none, otherwise a conflicting core
	 */
	boost::optional<FormulasT> isInfeasible(carl::Variable var, const FormulaT& f);
	
	/**
	 * Takes a conflicting core as a reason and explains it by an explanation as described in the MCSAT / NLSAT paper.
	 */
	FormulaT explain(carl::Variable var, const FormulasT& reason, const FormulaT& implication);
};

std::ostream& operator<<(std::ostream& os, const NLSAT& nl) {
	os << "NLSAT:" << std::endl;
	os << "## Model: " << nl.mModel << std::endl;
	os << "## Constraints: " << nl.mConstraints << std::endl;
	os << "## Bounds: " << nl.mMVBounds << std::endl;
	return os;
}

}
}
