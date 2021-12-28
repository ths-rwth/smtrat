/**
 * @file NewCovering.cpp
 * @author Philip Kroll <Philip.Kroll@rwth-aachen.de>
 *
 * @version 2021-07-08
 * Created on 2021-07-08.
 */

#include "NewCoveringModule.h"

namespace smtrat {
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
size_t NewCoveringModule<Settings>::addConstraintsSAT() {
	// Hard case:
	//  Recheck the unknown constraints with the last satisfying assignment
	SMTRAT_LOG_DEBUG("smtrat.covering", "Rechecking the unknown constraints with the last satisfying assignment");
	std::size_t lowestLevelWithUnsatisfiedConstraint = 0;
	bool foundUnsatisfiedConstraint = false;
	while (lowestLevelWithUnsatisfiedConstraint < mVariableOrdering.size() && !foundUnsatisfiedConstraint) {
		SMTRAT_LOG_DEBUG("smtrat.covering", "Checking level " << lowestLevelWithUnsatisfiedConstraint << "/" << mVariableOrdering.size());
		for (const auto& constraint : mUnknownConstraints) {
			if (carl::evaluate(constraint.constraint(), mLastAssignment) != true) {
				// This constraint is unsat with the last assignment
				SMTRAT_LOG_DEBUG("smtrat.covering", "Found unsatisfied constraint on level:" << lowestLevelWithUnsatisfiedConstraint);
				foundUnsatisfiedConstraint = true;
				break;
			}
		}
		lowestLevelWithUnsatisfiedConstraint++;
	}

	// We can add the new constraints to the backend now
	for (const auto& constraint : mUnknownConstraints) {
		backend.addConstraint(std::move(constraint.constraint()));
	}
	mUnknownConstraints.clear();

	return lowestLevelWithUnsatisfiedConstraint;
}

template<class Settings>
void NewCoveringModule<Settings>::removeConstraintsSAT() {
	// Easy case:
	// we can just remove the constraints and the corresponding stored information
	// this does not change the current satisfying assignment
	// Also: The satisfying assignment stays satisfying
	for (const auto& constraint : mRemoveConstraints) {
		backend.removeConstraint(std::move(constraint.constraint()));
	}
	mRemoveConstraints.clear();
}

template<class Settings>
void NewCoveringModule<Settings>::addConstraintsUNSAT() {
	// Easy case
	//  Add all unknown constraints to backend
	//  We can do this with no further calculations, as the model stays unsatisfiable
	for (const auto& constraint : mUnknownConstraints) {
		backend.addConstraint(std::move(constraint.constraint()));
	}
	mUnknownConstraints.clear();
}

template<class Settings>
bool NewCoveringModule<Settings>::removeConstraintsUNSAT() {
	// Hard case:
	//  We have to remove the constraints and the corresponding stored information
	//  This might include information in the old full coverings
	//  If not: the model stays unsatisfiable
	//  If yes: the model might become satisfiable or stays unsatisfiable -> Needs recalculation of the covering at level 0
	//  If level 0 is still full after removal of constraints: the model is still unsatisfiable
	//  If level 0 is not full after removal of constraints: the model might become satisfiable or stays unsatisfiable -> Needs recalculation off all the higher levels

	// First: remove all constraints from the backend
	for (const auto& constraint : mRemoveConstraints) {
		backend.removeConstraint(std::move(constraint.constraint()));
	}
	mRemoveConstraints.clear();

	// Second: Check if the covering on level 0 has changed
	bool hasChanged = backend.getCoveringInformation()[0].isUnknownCovering();

	// Third: If the covering has changed, we need to recompute it
	if (hasChanged) {
		backend.getCoveringInformation()[0].computeCovering();
	}

	return backend.getCoveringInformation()[0].isFullCovering();
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
	} else if (mLastAnswer == Answer::UNSAT || mLastAnswer == Answer::SAT) {
		if (mUnknownConstraints.empty() && mRemoveConstraints.empty()) {
			// We dont have any new constraints and can just return the last value derived by the backend
			// Why does this even happen??
			return mLastAnswer;
		}

		if (mRemoveConstraints.empty() && !mUnknownConstraints.empty()) {
			// we only have constraints to add, and no constraints to remove

			if (mLastAnswer == Answer::SAT) {
				// Hard case:
				auto lowestLevel = addConstraintsSAT();

				if (lowestLevel == mVariableOrdering.size() + 1) {
					// The assignment is still satisfiable
					return Answer::SAT;
				} else {
					// Remove all the data from the levels higher than lowestLevel
					backend.resetStoredData(lowestLevel);
				}
			} else {
				// Easy Case:
				addConstraintsUNSAT();
				// NOTE: Trivially the infeasible subset did not change
				return Answer::UNSAT;
			}

		} else if (!mRemoveConstraints.empty() && mUnknownConstraints.empty()) {
			// We only have constraints to remove, and no constraints to add

			if (mLastAnswer == Answer::SAT) {
				// Easy case
				removeConstraintsSAT();
				return Answer::SAT;
			} else {
				// Hard case
				bool stillFullCovering = removeConstraintsUNSAT();
				if (stillFullCovering) {
					// The assignment is still unsatisfiable

					// we have to recompute the infeasible subset
					mInfeasibleSubsets.push_back(backend.getInfeasibleSubset());
					SMTRAT_LOG_DEBUG("smtrat.covering", "Infeasible Subset: " << mInfeasibleSubsets.back());
					return Answer::UNSAT;
				} else {
					backend.resetStoredData(1);
					// TODO: This unnecessarily recomputes the covering for level 0 in the call to getUnsatCover
				}
			}
		} else if (!mRemoveConstraints.empty() && !mUnknownConstraints.empty()) {
			// We have both constraints to add and constraints to remove
			// First make sure that the vectors are disjoint
			FormulasT intersection;
			// we need to sort both vectors to make sure that the intersection is correct
			std::sort(mRemoveConstraints.begin(), mRemoveConstraints.end());
			std::sort(mUnknownConstraints.begin(), mUnknownConstraints.end());
			std::set_intersection(mUnknownConstraints.begin(), mUnknownConstraints.end(), mRemoveConstraints.begin(), mRemoveConstraints.end(), std::back_inserter(intersection));

			if (intersection.size() > 0) {
				// There is an intersection between the two vectors
				// This means that we need to remove the intersection from the remove constraints
				// NOTE: This is a rare case, but it can happen
				// TODO: remove intersection from mRemoveConstraints or mUnknownConstraints???
				SMTRAT_LOG_DEBUG("smtrat.covering", "Intersection between unknown and remove constraints: " << intersection);
				for (const auto& constraint : intersection) {
					mRemoveConstraints.erase(std::remove(mRemoveConstraints.begin(), mRemoveConstraints.end(), constraint), mRemoveConstraints.end());
				}
			}

			if (mLastAnswer == Answer::SAT) {
				// first trivially remove the constraints
				removeConstraintsSAT();
				// then add the constraints
				auto lowestLevel = addConstraintsSAT();
				if (lowestLevel == mVariableOrdering.size() + 1) {
					// The assignment is still satisfiable
					return Answer::SAT;
				} else {
					// Remove all the data from the levels higher than lowestLevel
					backend.resetStoredData(lowestLevel);
				}
			} else {
				// first trivially add the constraints
				addConstraintsUNSAT();
				// then remove the constraints
				bool stillFullCovering = removeConstraintsUNSAT();
				if (stillFullCovering) {
					// The assignment is still unsatisfiable
					// we have to recompute the infeasible subset
					mInfeasibleSubsets.push_back(backend.getInfeasibleSubset());
					SMTRAT_LOG_DEBUG("smtrat.covering", "Infeasible Subset: " << mInfeasibleSubsets.back());
					return Answer::UNSAT;
				} else {
					backend.resetStoredData(1);
				}
			}
		}
	} else {
		// The last call returned UNKNOWN
		// we have to delete all stored information and completely re-initialize the backend
		backend.resetStoredData(0);
		backend.resetDerivationToConstraintMap();
	}

	// Todo: for the incremental call we dont have to start at level 0 -> we could start at the lowest level with an unsatisfied constraint -> this would be faster
	mLastAnswer = backend.getUnsatCover(0);

	SMTRAT_LOG_DEBUG("smtrat.covering", "Check Core returned: " << mLastAnswer);

	if (mLastAnswer == Answer::UNSAT) {
		mInfeasibleSubsets.push_back(backend.getInfeasibleSubset());
		SMTRAT_LOG_DEBUG("smtrat.covering", "Infeasible Subset: " << mInfeasibleSubsets.back());
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
