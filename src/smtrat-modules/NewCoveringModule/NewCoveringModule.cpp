/**
 * @file NewCovering.cpp
 * @author Philip Kroll <Philip.Kroll@rwth-aachen.de>
 *
 * @version 2021-07-08
 * Created on 2021-07-08.
 */

#include "NewCoveringModule.h"

namespace smtrat {
// Todo add preprocessor?
template<class Settings>
NewCoveringModule<Settings>::NewCoveringModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager)
	: Module(_formula, _conditionals, _manager) {
	SMTRAT_LOG_DEBUG("smtrat.covering", "Init New Covering Module")
}

template<class Settings>
NewCoveringModule<Settings>::~NewCoveringModule() {}

template<class Settings>
bool NewCoveringModule<Settings>::informCore(const FormulaT& _constraint) {

	// Gather all possibly occuring variables
	_constraint.gatherVariables(mVariables);

	return true;
}

template<class Settings>
void NewCoveringModule<Settings>::init() {}

template<class Settings>
bool NewCoveringModule<Settings>::addCore(ModuleInput::const_iterator _subformula) {
	// Incremental call
	assert(_subformula->formula().getType() == carl::FormulaType::CONSTRAINT);
	mUnknownConstraints.push_back(_subformula->formula());
	SMTRAT_LOG_DEBUG("smtrat.covering", "Adding new unknown constraint: " << _subformula->formula().constraint());

	//_subformula->formula().gatherVariables(mVariables);

	carl::carlVariables newVars;
	_subformula->formula().gatherVariables(newVars);
	for (const auto& v : newVars) {
		if (!mVariables.has(v)) {
			// How can that even happen?
			SMTRAT_LOG_DEBUG("smtrat.covering", "Unknown Variable in new constraint: " << v);
			assert(false);
		}
	}
	return true;
}

template<class Settings>
void NewCoveringModule<Settings>::removeCore(ModuleInput::const_iterator _subformula) {
	// Backtracking
	assert(_subformula->formula().getType() == carl::FormulaType::CONSTRAINT);
	mRemoveConstraints.push_back(_subformula->formula());
	SMTRAT_LOG_DEBUG("smtrat.covering", "Adding to remove constraint: " << _subformula->formula().constraint());
}

template<class Settings>
void NewCoveringModule<Settings>::updateModel() const {
	clearModel();
	for (const auto& pair : mLastAssignment) {
		mModel.assign(pair.first, pair.second);
	}
}

template<class Settings>
void NewCoveringModule<Settings>::passConstraintInformationToBackend() {
	// remove the given constraints from the backend
	for (const auto& constraint : mRemoveConstraints) {
		backend.removeConstraint(constraint.constraint());
	}
	mRemoveConstraints.clear();

	// Add all unknown constraints to backend
	for (const auto& constraint : mUnknownConstraints) {
		backend.addConstraint(constraint.constraint());
	}
	mUnknownConstraints.clear();
}

template<class Settings>
Answer NewCoveringModule<Settings>::checkCore() {
	SMTRAT_LOG_DEBUG("smtrat.covering", "Check Core called with unknown constraints: " << mUnknownConstraints);
	SMTRAT_LOG_DEBUG("smtrat.covering", "Check Core called with remove constraints: " << mRemoveConstraints);
	SMTRAT_LOG_DEBUG("smtrat.covering", "Last Answer: " << mLastAnswer);
	SMTRAT_LOG_DEBUG("smtrat.covering", "Check Core called with last assignment: " << mLastAssignment);

	// Check if this is the first time checkCore is called
	if (mVariableOrdering.empty()) {
		// Init variable odering

		SMTRAT_LOG_DEBUG("smtrat.covering", "Got Variables: " << mVariables);

		// Just take the current ordering of the set -> we do heuristics later
		std::copy(mVariables.as_vector().begin(), mVariables.as_vector().end(), std::back_inserter(mVariableOrdering));

		SMTRAT_LOG_DEBUG("smtrat.covering", "Got Variable Ordering : " << mVariableOrdering);

		// init backend
		backend.init(mVariableOrdering);

		// Add unknown constraints to backend
		for (const auto& constraint : mUnknownConstraints) {
			// Asserts that it is indeed a constraint
			backend.addConstraint(constraint.constraint());
		}

		mUnknownConstraints.clear();
	} else if (mLastAnswer == Answer::SAT) {
		// This is either an incremental call or a backtracking call (or both)

		if (mUnknownConstraints.empty() && mRemoveConstraints.empty()) {
			// We dont have any new constraints and can just return the last value derived by the backend
			// Why does this even happen??
			return mLastAnswer;
		} else if (!mUnknownConstraints.empty() && mRemoveConstraints.empty()) {
			// This is an ONLY incremental call as we have new unknown constraints but no constraints to remove
			SMTRAT_LOG_DEBUG("smtrat.covering", "Incremental ONLY Call with new constraints: " << mUnknownConstraints << " and old assignment: " << mLastAssignment);

			// Recheck the unknown constraints with the last satisfying assignment
			std::size_t lowestLevelWithUnsatisfiedConstraint = mVariables.size() + 1;

			for (const auto& constraint : mUnknownConstraints) {
				// if (backend.check(constraint.constraint()) == Answer::UNSAT) {
				if (carl::evaluate(constraint.constraint(), mLastAssignment) != true) {
					// This constraint is unsat with the last assignment
					SMTRAT_LOG_DEBUG("smtrat.covering", "This constraint is unsat with the last assignment: " << constraint.constraint());

					// We can substract 1 from level because we dont have constant polynomials
					std::size_t level = cadcells::helper::level_of(mVariableOrdering, constraint.constraint().lhs()) - 1;
					lowestLevelWithUnsatisfiedConstraint = std::min(lowestLevelWithUnsatisfiedConstraint, level);

				} else {
					// This constraint is sat with the last assignment
					SMTRAT_LOG_DEBUG("smtrat.covering", "This constraint is sat with the last assignment: " << constraint.constraint());
				}
			}

			// reset the backend for all levels higher and including the lowest level with an unsatisfied constraint
			if (lowestLevelWithUnsatisfiedConstraint < mVariables.size() + 1) {
				SMTRAT_LOG_DEBUG("smtrat.covering", "Resetting backend for levels higher or equal to " << lowestLevelWithUnsatisfiedConstraint);
				backend.resetStoredData(lowestLevelWithUnsatisfiedConstraint);
			} else {
				SMTRAT_LOG_DEBUG("smtrat.covering", "No unsatisfied constraints found -> we can trivially return SAT again with the same assignment");
				// Todo: can we add the constraint to the backend here already?
				return Answer::SAT;
			}

			passConstraintInformationToBackend();

		} else if (mUnknownConstraints.empty() && !mRemoveConstraints.empty()) {
			// This is an ONLY backtracking call as we only have constraints to remove but no new unknown constraints
			// not supported yet, we just reset all data in the backend
			// TODO : FULLY SUPPORT BACKTRACKING!
			SMTRAT_LOG_DEBUG("smtrat.covering", "Backtracking ONLY Call with remove constraints: " << mRemoveConstraints);

			passConstraintInformationToBackend();

		} else if (!mUnknownConstraints.empty() && !mRemoveConstraints.empty()) {
			// Both incremental call and backtracking as we have constraints to remove new unknown constraints
			// What do we do? first do backtracking and then do incremental?? -> Ask Jasper
			// not supported, we the reset all the data and make a fresh start

			SMTRAT_LOG_DEBUG("smtrat.covering", "Backtracking and Incremental Call with new constraints: " << mUnknownConstraints << " and remove constraints: " << mRemoveConstraints);

			passConstraintInformationToBackend();
		}
	} else {

		// As the last iteration was UNSAT we dont have any saved information in the backend
		// We can just add and remove the new given constraints

		passConstraintInformationToBackend();
	}

	// Todo: for the incremental call we dont have to start at level 0 -> we could start at the lowest level with an unsatisfied constraint -> this would be faster
	// In the current implementation we still calculate the new unsat-cells for levels that are satisfied with the last assignment -> this is not necessary
	mLastAnswer = backend.getUnsatCover(0);

	SMTRAT_LOG_DEBUG("smtrat.covering", "Check Core returned: " << mLastAnswer);

	if (mLastAnswer == Answer::UNSAT) {
		mInfeasibleSubsets.push_back(backend.getInfeasibleSubset());
		mLastAssignment.clear(); // There is no satisfying assignment

	} else if (mLastAnswer == Answer::SAT) {
		mLastAssignment = backend.getCurrentAssignment();

	} else {
		// Answer is UNKNOWN and something went wrong
		SMTRAT_LOG_DEBUG("smtrat.covering", "Backend encountered an error: " << mLastAnswer);

		// remove all stored information in the backend
		backend.resetStoredData(0);
		mLastAssignment.clear(); // There is no satisfying assignment
	}
	updateModel();

	return mLastAnswer;
}
} // namespace smtrat

#include "Instantiation.h"
