#pragma once

#include "../../../Common.h"

#include "AssignmentFinder.h"

#include <boost/optional.hpp>

namespace smtrat {
namespace nlsat {

class NLSAT {
private:
	std::vector<FormulaT> mConstraints;
	std::vector<FormulaT> mMVBounds;
	Model mModel;
	std::vector<carl::Variable> mVariables;
	std::vector<FormulaT> mAssignments;
	
	FormulaT resolveNegation(const FormulaT& f) const;
	
public:
	/// Add a new constraint
	void pushConstraint(const FormulaT& f);
	/// Remove a constraint
	void popConstraint(const FormulaT& f);
	/// Add a new assignment
	void pushAssignment(carl::Variable v, const ModelValue& mv, const FormulaT& f);
	/// Remove an assignment
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
	 * Takes a conflicting core as a reason and explains it by 
	 */
	FormulaT explain(carl::Variable var, const FormulasT& reason, const FormulaT& implication);
};

}
}
