/**
 * @file NewCovering.cpp
 * @author Philip Kroll <Philip.Kroll@rwth-aachen.de>
 *
 * @version 2021-07-08
 * Created on 2021-07-08.
 */

#include "NewCoveringModule.h"

namespace smtrat {
//Todo add preprocessor?
template<class Settings>
NewCoveringModule<Settings>::NewCoveringModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager)
	: Module(_formula, _conditionals, _manager) {
	SMTRAT_LOG_DEBUG("smtrat.covering", "Init New Covering Module")
}

template<class Settings>
NewCoveringModule<Settings>::~NewCoveringModule() {}

template<class Settings>
bool NewCoveringModule<Settings>::informCore(const FormulaT& _constraint) {
	SMTRAT_LOG_DEBUG("smtrat.covering", "Got constraint: " << _constraint.constraint());
	mUnknownConstraints.push_back(_constraint);
	return true; 
}

template<class Settings>
void NewCoveringModule<Settings>::init() {}

template<class Settings>
bool NewCoveringModule<Settings>::addCore(ModuleInput::const_iterator _subformula) {
	//Incremental call
	//TODO: is it possible that new (unknown) Variable are in the new constraints?
	mUnknownConstraints.push_back(_subformula->formula());
	return true; 
}

template<class Settings>
void NewCoveringModule<Settings>::removeCore(ModuleInput::const_iterator _subformula) {
	//Backtracking
	assert(false);
	// Your code.
}

template<class Settings>
void NewCoveringModule<Settings>::updateModel() const {
	clearModel();
	if (solverState() == Answer::SAT) {
		mModel.update(mLastModel, false);
	}
}

template<class Settings>
Answer NewCoveringModule<Settings>::checkCore() {
	SMTRAT_LOG_DEBUG("smtrat.covering", "Check Core called with unknown constraints: " << mUnknownConstraints << " and known constraints: " << mKnownConstraints);

	//Check if this is the first time checkCore is called
	if (mVariableOrdering.empty()) {
		//Init variable odering
		
		for(const FormulaT& formula : mUnknownConstraints){
			formula.gatherVariables(mVariables);
		}

		SMTRAT_LOG_DEBUG("smtrat.covering", "Got Variables: " << mVariables);

		//Just take the current ordering of the set -> we do heuristics later
		std::copy(mVariables.as_vector().begin(), mVariables.as_vector().end(), std::back_inserter(mVariableOrdering));

		SMTRAT_LOG_DEBUG("smtrat.covering", "Got Variable Ordering : " << mVariableOrdering);

		//init backend
		backend.init(mVariableOrdering);

		//Add unknown constraints to backend
		for(const auto& constraint : mUnknownConstraints){
			//Asserts that it is indeed a constraint
			backend.addConstraint(constraint.constraint()) ;
		}

	} else if (backend.dimension() != mVariables.size()) {
		//This is an incremental call, we have more Variable than before and are out of sync with the backend and the Helpers
		//Add unknown polynomials to PolyPool

		//TODO: Change Var ordering in PolyPool
		assert(false);
	}

	else {
		//This is either an incremental call or a backtracking call but the set of known variables is the same
		//Add unknown polynomials to PolyPool

		assert(false);
	}

	Answer answer = backend.getUnsatCover(0);

	return answer;
}
} // namespace smtrat

#include "Instantiation.h"
