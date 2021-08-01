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
	mPolynomials.emplace_back(_constraint.constraint().lhs());
	_constraint.gatherVariables(mVariables);
	return true; // This should be adapted according to your implementation.
}

template<class Settings>
void NewCoveringModule<Settings>::init() {}

template<class Settings>
bool NewCoveringModule<Settings>::addCore(ModuleInput::const_iterator _subformula) {
	//Incremental call
	//TODO: is it possible that new (unknown) Variable are in the new constraints?
	mPolynomials.emplace_back(_subformula->formula().constraint().lhs());
	return true; // This should be adapted according to your implementation.
}

template<class Settings>
void NewCoveringModule<Settings>::removeCore(ModuleInput::const_iterator _subformula) {
	//Backtracking
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
	//Check if this is the first time checkCore is called
	SMTRAT_LOG_DEBUG("smtrat.covering", "Check Core called with new polynomials: " << mPolynomials);

	if (mVariableOrdering.empty()) {
		//Init variable odering
		//Just take the current ordering of the set -> we do heuristics later
		std::copy(mVariables.begin(), mVariables.end(), std::back_inserter(mVariableOrdering));

		SMTRAT_LOG_DEBUG("smtrat.covering", "Dimensions dont match -> make new variable ordering: " << mVariableOrdering);


		// 	//init PolyPool
		helpers.mPool = std::make_shared<smtrat::cadcells::datastructures::PolyPool>(mVariableOrdering);
		helpers.mProjections = std::make_shared<smtrat::cadcells::datastructures::Projections>(*helpers.mPool);

		//TODO: add move operator
		for (const carl::MultivariatePolynomial<mpq_class>& poly : mPolynomials) {
			helpers.mPool->insert(poly);
		}
		mPolynomials.clear();
		SMTRAT_LOG_DEBUG("smtrat.covering", "Initialised PolyPool");
		SMTRAT_LOG_DEBUG("smtrat.covering", "Initialised Projections");


		SMTRAT_LOG_DEBUG("smtrat.covering", "Got Ordering: " << helpers.mPool->var_order());

	} else if(backend.dimension() != mVariables.size()){
		//Due to an incremental call, we have more Variable than before and are out of sync with the backend and the Helpers

		//TODO: Change Var ordering in PolyPool
	}

	else {
		//This is either an incremental call or a backtracking call
		//Add unknown polynomials to PolyPool
		//TODO: add move operator
		SMTRAT_LOG_DEBUG("smtrat.covering", "Insert " << mPolynomials << " into PolyPool");

		for (const carl::MultivariatePolynomial<mpq_class>& poly : mPolynomials) {
			helpers.mPool->insert(poly) ;
		}

		mPolynomials.clear();
	}
	
	

	return Answer::UNKNOWN; // This should be adapted according to your implementation.
}
} // namespace smtrat

#include "Instantiation.h"
