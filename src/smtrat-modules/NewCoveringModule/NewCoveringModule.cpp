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
	SMTRAT_LOG_DEBUG("smtrat.covering", "Init New Covering Module");
	// Pass informations about the settings to the statistics
	SMTRAT_STATISTICS_CALL(getStatistics().setVariableOrderingType(mcsat::get_name(Settings::variableOrderingStrategy)));
	SMTRAT_STATISTICS_CALL(getStatistics().setCoveringHeuristicType(cadcells::representation::get_name(Settings::covering_heuristic)));
	SMTRAT_STATISTICS_CALL(getStatistics().setOperatorType(cadcells::operators::get_name(Settings::op)));
	SMTRAT_STATISTICS_CALL(getStatistics().setSamplingAlgorithm(get_name(Settings::sampling_algorithm)));
	SMTRAT_STATISTICS_CALL(getStatistics().setIsSampleOutsideAlgorithm(get_name(Settings::is_sample_outside_algorithm)));
}

template<class Settings>
NewCoveringModule<Settings>::~NewCoveringModule() {}

template<class Settings>
bool NewCoveringModule<Settings>::informCore(const FormulaT& _constraint) {
	// Gather all possible constraints for the initial (complete!) variable ordering
	assert(_constraint.type() == carl::FormulaType::CONSTRAINT);
	mAllConstraints.push_back(_constraint.constraint());
	return true;
}

template<class Settings>
void NewCoveringModule<Settings>::init() {}

template<class Settings>
bool NewCoveringModule<Settings>::addCore(ModuleInput::const_iterator _subformula) {
	// Incremental call
	assert(_subformula->formula().type() == carl::FormulaType::CONSTRAINT);
	mUnknownConstraints.push_back(_subformula->formula());
	SMTRAT_LOG_DEBUG("smtrat.covering", "Adding new unknown constraint: " << _subformula->formula().constraint());
	return true;
}

template<class Settings>
void NewCoveringModule<Settings>::removeCore(ModuleInput::const_iterator _subformula) {
	// Backtracking
	assert(_subformula->formula().type() == carl::FormulaType::CONSTRAINT);
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
	SMTRAT_LOG_DEBUG("smtrat.covering", "Adding constraints: " << mUnknownConstraints);
	// Hard case:
	//  Recheck the unknown constraints with the last satisfying assignment
	SMTRAT_LOG_DEBUG("smtrat.covering", "Rechecking the unknown constraints with the last satisfying assignment");
	std::size_t lowestLevelWithUnsatisfiedConstraint = mVariableOrdering.size()+1;
	bool foundUnsatisfiedConstraint = false;

	std::map<size_t, std::vector<ConstraintT>> constraintsByLevel;

	for(const auto& formula : mUnknownConstraints) {
		ConstraintT constraint = formula.constraint();
		size_t level = helper::level_of(mVariableOrdering, constraint.lhs()) - 1;
		constraintsByLevel[level].push_back(std::move(constraint));
	}
	mUnknownConstraints.clear();

	SMTRAT_LOG_DEBUG("smtrat.covering", "Build constraint map: " << constraintsByLevel);

	// Now iterate over the constraints by level, starting with lowest first (the keys in a std::map are implicitly sorted using std::less)
	for (const auto& levelConstraints : constraintsByLevel) {
		SMTRAT_LOG_DEBUG("smtrat.covering", "Checking level " << levelConstraints.first);
		if (foundUnsatisfiedConstraint) break;
		for (const auto& constraint : levelConstraints.second) {
			if (carl::evaluate(constraint.constr(), mLastAssignment) != true) {
				// This constraint is unsat with the last assignment
				SMTRAT_LOG_DEBUG("smtrat.covering", "Found unsatisfied constraint on level:" << levelConstraints.first);
				foundUnsatisfiedConstraint = true;
				lowestLevelWithUnsatisfiedConstraint = levelConstraints.first;
				break ;
			}
		}
	}

	// We can add the new constraints to the backend now
	for (const auto& levelConstraints : constraintsByLevel) {
		backend.addConstraint(levelConstraints.first, std::move(levelConstraints.second));
	}
	constraintsByLevel.clear();

	return lowestLevelWithUnsatisfiedConstraint ;
	
}

template<class Settings>
void NewCoveringModule<Settings>::removeConstraintsSAT() {
	SMTRAT_LOG_DEBUG("smtrat.covering", "Removing constraints: " << mRemoveConstraints);
	// Easy case:
	// we can just remove the constraints and the corresponding stored information
	// this does not change the current satisfying assignment/ satisfyability of the given set of constraints
	for (const auto& constraint : mRemoveConstraints) {
		backend.removeConstraint(std::move(constraint.constraint()));
	}
	mRemoveConstraints.clear();
}

template<class Settings>
void NewCoveringModule<Settings>::addConstraintsUNSAT() {
	SMTRAT_LOG_DEBUG("smtrat.covering", "Adding constraints: " << mUnknownConstraints);
	// Easy case:
	//  Add all unknown constraints to backend
	//  We can do this with no further calculations, as the model stays unsatisfiable
	for (const auto& constraint : mUnknownConstraints) {
		backend.addConstraint(std::move(constraint.constraint()));
	}
	mUnknownConstraints.clear();
}

template<class Settings>
bool NewCoveringModule<Settings>::removeConstraintsUNSAT() {
	SMTRAT_LOG_DEBUG("smtrat.covering", "Removing constraints: " << mRemoveConstraints);
	assert(backend.getCoveringInformation()[0].isFullCovering());
	// Hard case:
	//  We have to remove the constraints and the corresponding stored information (derivations with the constraint as origin)
	//  This might include information in the stored full coverings
	//  If not: Nothing changes and the model stays unsatisfiable
	//  If yes: the model might become satisfiable or stays unsatisfiable -> Needs recalculation of the covering at level 0
	//  If level 0 is still full after removal of constraints: the model is still unsatisfiable
	//  If level 0 is not full after removal of constraints: the model might become satisfiable or stays unsatisfiable -> Needs recalculation off all the higher levels : TODO Ask Jasper if this is correct

	// First: remove all constraints from the backend, this also removes the corresponding derivations and invalidates the coverings, if they used a removed derivations
	for (const auto& constraint : mRemoveConstraints) {
		backend.removeConstraint(std::move(constraint.constraint()));
	}
	mRemoveConstraints.clear();

	// Second: Check if the covering on level 0 has changed/ was invalidated
	bool hasChanged = backend.getCoveringInformation()[0].isUnknownCovering();

	SMTRAT_LOG_DEBUG("smtrat.covering", "Covering on level 0 has changed: " << hasChanged);

	// Third: If the covering has changed, we need to recompute it
	if (hasChanged) {
		backend.getCoveringInformation()[0].computeCovering();
	}

	SMTRAT_LOG_DEBUG("smtrat.covering", "Covering on level is still full: " << backend.getCoveringInformation()[0].isFullCovering());

	return backend.getCoveringInformation()[0].isFullCovering();
}

template<typename Settings>
Answer NewCoveringModule<Settings>::checkCore() {

	SMTRAT_STATISTICS_CALL(getStatistics().called());

	SMTRAT_LOG_DEBUG("smtrat.covering", "Check Core called with unknown constraints: " << mUnknownConstraints);
	SMTRAT_LOG_DEBUG("smtrat.covering", "Check Core called with remove constraints: " << mRemoveConstraints);
	SMTRAT_LOG_DEBUG("smtrat.covering", "Last Answer: " << mLastAnswer);
	SMTRAT_LOG_DEBUG("smtrat.covering", "Check Core called with last assignment: " << mLastAssignment);

	// Check if this is the first time checkCore is called
	if (mVariableOrdering.empty()) {

		// Init variable odering, we use the variable ordering which was declared in the settings
		mVariableOrdering = mcsat::calculate_variable_order<Settings::variableOrderingStrategy>(mAllConstraints);

		SMTRAT_STATISTICS_CALL(getStatistics().setDimension(mVariableOrdering.size()));

		// We can clear mAllConstraints now, as we don't need it anymore -> Its only needed to calculate the variable ordering
		mAllConstraints.clear();

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

			SMTRAT_STATISTICS_CALL(getStatistics().calledIncrementalOnly());

			if (mLastAnswer == Answer::SAT) {
				// Hard case:
				auto lowestLevel = addConstraintsSAT();

				if (lowestLevel == mVariableOrdering.size() + 1) {
					// The assignment is still satisfiable
					return Answer::SAT;
				} else {
					// Remove all the data from the levels higher than lowestLevel
					SMTRAT_LOG_DEBUG("smtrat.covering", "Removing data from level " << lowestLevel);
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

			SMTRAT_STATISTICS_CALL(getStatistics().calledBacktrackingOnly());

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
				}
			}
		} else if (!mRemoveConstraints.empty() && !mUnknownConstraints.empty()) {

			SMTRAT_STATISTICS_CALL(getStatistics().calledIncrementalAndBacktracking());

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
				// We remove the intersection from the remove constraints
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
					//delete everything, but keep level 0
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

	// As getUnsatCover is recursive we always have to start at level 0 
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

	updateModel(); // Update the model according to the last assignment from the backend

	return mLastAnswer;
}
} // namespace smtrat
#include "Instantiation.h"
