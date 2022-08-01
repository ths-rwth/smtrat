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

// Import Datastructures used for caching etc.
#include <smtrat-cadcells/datastructures/polynomials.h>
#include <smtrat-cadcells/datastructures/projections.h>

#include <smtrat-cadcells/operators/operator_mccallum.h>
#include <smtrat-cadcells/representation/heuristics.h>

#include <smtrat-mcsat/variableordering/VariableOrdering.h>

#include "Backend.h"
#include "LevelWiseInformation.h"

#include "NewCoveringStatistics.h"
#include "Sampling.h"

namespace smtrat {

template<typename Settings>
class NewCoveringModule : public Module {
private:
    // List of constraints that have not been passed to the backend
    FormulasT mUnknownConstraints;

    // List of constraints that have to be removed from the backend (For Backtracking)
    FormulasT mRemoveConstraints;

    // List of all constraints (Only used once for the initial variable ordering and then cleared)
    std::vector<ConstraintT> mAllConstraints;

    // Variable Ordering, Initialized in checkCore
    std::vector<carl::Variable> mVariableOrdering;

    // The Result of the last check, unkown if not run yet
    Answer mLastAnswer = Answer::UNKNOWN;

	// Contains the last assignment which satisfied all the given known constraints (empty otherwise)
	carl::Assignment<RAN> mLastAssignment;

    // The actual algorithm
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

    /**
     * Processes the current answer, i.e. computes a model or adds the infeasible subset.
     * 
     */
    void processAnswer();

    // ----Backend Interfaces for addition and removal of constraints if the previous call was SAT ----

    /**
     * @brief Adds the given constraint to the backend
     * @return the lowest level with an unsatisfied new constraint
     * @note returns mVariableOrdering.size()+1 if all new constraints are satisfied
     * @note If not all new constraints are satisfied the
     */
    size_t addConstraintsSAT();

    /**
     * @brief Removes the given constraints from the backend
     * @note This also removes all stored information about the removed constraints
     */
    void removeConstraintsSAT();

    // ----Backend Interfaces for addition and removal of constraints if the previous call was UNSAT ----

    /**
     * Adds the given constraint to the backend
     *
     */
    void addConstraintsUNSAT();

    /**
     * Removes the given constraints from the backend
     * Also removes all stored information about the removed constraints
     * @return True: If the model is still unsat after removing the constraints
     * 	   False: If the model might needs recomputation for the higher levels
     */
    bool removeConstraintsUNSAT();

    /**
     * @brief The actual backtracking algorithm, which is called when we have constraints to add and no constraints to remove
     *
     * Removes all cells which were created as a rest of the constraints which are to be removed
     * if level 0 is still fully covered after removing the constraints UNSAT is returned
     * Otherwise std::nullopt is returned and level 1 is newly sampled and the algorithm starts again from level 1
     *
     * @return std::optional<Answer>, which contains the answer if it can be deduced directly
     */
    std::optional<Answer> doBacktracking();

    /**
     * @brief The actual incremental algorithm, which is called when we have constraints to add and no constraints to remove
     *
     * Tests the new constaints with the last satisfying assignment, if the new constraints are also satisfied.
     * If the new constraints are all satisfied SAT is returned accordingly
     * Otherwise std::nullopt is returned and the stored information from the lowest level with an unsatisfied new constraint is removed
     *
     * @return std::optional<Answer>, which contains the answer if it can be deduced directly
     */
    std::optional<Answer> doIncremental();

    /**
     * @brief Algorithms which contains backtracking and incremental checking, its called when we have constraints to add and constraints to remove
     *
     * @return std::optional<Answer>, which contains the answer if it can be deduced directly
     */
    std::optional<Answer> doIncremtalAndBacktracking();
};
} // namespace smtrat
