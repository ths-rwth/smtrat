/**
 * @file NewCoveringModule.h
 * @author Philip Kroll <Philip.Kroll@rwth-aachen.de>
 *
 * @version 2021-07-08
 * Created on 2021-07-08.
 */

#pragma once

#include "NewCoveringSettings.h"
#include <boost/container/flat_set.hpp>
#include <smtrat-solver/Module.h>

#include <smtrat-cadcells/common.h>

//Import Datastructures used for caching etc.
#include <smtrat-cadcells/datastructures/polynomials.h>
#include <smtrat-cadcells/datastructures/projections.h>

#include <smtrat-cadcells/operators/operator_mccallum.h>
#include <smtrat-cadcells/representation/heuristics.h>

#include "Backend.h"

namespace smtrat {

template<typename Settings>
class NewCoveringModule : public Module {
private:
	//List of constraints that have not been passed to the backend
	FormulasT mUnknownConstraints;

	//List of constraints that have to be removed from the backend (For Backtracking)
	FormulasT mRemoveConstraints;

	//Set of all known Variables
	carl::carlVariables mVariables;

	//Variable Ordering, Initialized in checkCore
	std::vector<carl::Variable> mVariableOrdering;

	//The Result of the last check, unkown if not run yet
	Answer mLastAnswer = Answer::UNKNOWN;

	//Contains the last assignment which satisfied all the given known constraints (empty otherwise)
	carl::ran_assignment<Rational> mLastAssignment;

	//The actual algorithm
	Backend<Settings> backend;

public:
	using SettingsType = Settings;

	NewCoveringModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager = nullptr);

	~NewCoveringModule();

	// Main interfaces.
	/**
			 * Informs the module about the given constraint. It should be tried to inform this
			 * module about any constraint it could receive eventually before assertSubformula
			 * is called (preferably for the first time, but at least before adding a formula
			 * containing that constraint).
			 * @param _constraint The constraint to inform about.
			 * @return false, if it can be easily decided whether the given constraint is inconsistent;
			 *		  true, otherwise.
			 */
	bool informCore(const FormulaT& _constraint);

	/**
			 * Informs all backends about the so far encountered constraints, which have not yet been communicated.
			 * This method must not and will not be called more than once and only before the first runBackends call.
			 */	
	void init();

	/**
			 * The module has to take the given sub-formula of the received formula into account.
			 *
			 * @param _subformula The sub-formula to take additionally into account.
			 * @return false, if it can be easily decided that this sub-formula causes a conflict with
			 *		  the already considered sub-formulas;
			 *		  true, otherwise.
			 */
	bool addCore(ModuleInput::const_iterator _subformula);

	/**
			 * Removes the subformula of the received formula at the given position to the considered ones of this module.
			 * Note that this includes every stored calculation which depended on this subformula, but should keep the other
			 * stored calculation, if possible, untouched.
			 *
			 * @param _subformula The position of the subformula to remove.
			 */
	void removeCore(ModuleInput::const_iterator _subformula);

	/**
			 * Updates the current assignment into the model.
			 * Note, that this is a unique but possibly symbolic assignment maybe containing newly introduced variables.
			 */
	void updateModel() const;

	/**
			 * Checks the received formula for consistency.
			 * @return True,	if the received formula is satisfiable;
			 *		 False,   if the received formula is not satisfiable;
			 *		 Unknown, otherwise.
			 */
	Answer checkCore();
};
} // namespace smtrat
