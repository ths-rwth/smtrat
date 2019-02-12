/**
 * @file FouMoModule.h
 * @author Dustin Huetter <dustin.huetter@rwth-aachen.de>
 *
 * @version 2014-12-01
 * Created on 2014-12-01.
 */

#pragma once

#include <smtrat-solver/Module.h>
#include "FouMoSettings.h"
namespace smtrat
{
 
    typedef std::pair<FormulaT, std::shared_ptr<std::vector<FormulaT>>> SingleFormulaOrigins;
    typedef std::map<FormulaT, std::shared_ptr<std::vector<FormulaT>>> FormulaOrigins;
    typedef std::map<carl::Variable, std::pair< std::vector<SingleFormulaOrigins>, std::vector<SingleFormulaOrigins>>> VariableUpperLower;
    /**
     * A module which applies the Fourier-Motzkin algorithm.
     */ 
    template<typename Settings>
    class FouMoModule : public Module
    {
        private:
            // Stores the current inequalities
            FormulaOrigins mProc_Constraints;
            // Stores the inequalities of all iterations
            std::vector< FormulaOrigins > mRecent_Constraints;  
            // Stores the equalities
            FormulaOrigins mEqualities;
            // Stores the disequalities
            FormulaOrigins mDisequalities;
            // Stores the order in which the variables were eliminated
            std::vector< carl::Variable > mElim_Order;
            // Stores the deleted constraints, just as they worked as an upper respectively lower
            // bound when eliminating the corresponding variable. The variables and their corresponding
            // upper/lower constraints are saved in the order given by mElim_Order
            VariableUpperLower mDeleted_Constraints;  
            // Stores constructed assignments for the occuring variables when a solution was found
            mutable std::map< carl::Variable, Rational > mVarAss;
            // Stores whether we found a valid solution in this module
            bool mCorrect_Solution;
            // Stores whether at least one non-linear term occured
            bool mNonLinear;
            // Stores whether the current instance contains only integer resp. real variables
            enum VAR_DOM
            {
                INT,
                UNKNOWN
            }; 
            VAR_DOM mDom;
            
            
            /**
             * @param curr_constraints Contains the constraints for which a preferably good
             *                         variable is chosen
             * @param var_corr_constr  After the procedure contains the chosen variable and 
             *                         the constraints for the elimination step
             */
            void gatherUpperLower( FormulaOrigins& curr_constraints, VariableUpperLower& var_corr_constr );
            
            /**
             * @param upper_constr Pointer to the constraint corresponding to an upper bound of corr_var          *                         variable is chosen
             * @param lower_constr Pointer to the constraint corresponding to a lower bound of corr_var
             * @param corr_var     Variable that shall be eliminated
             * @return             Pointer to the constraint resulting from the combination
             */
            FormulaT combineUpperLower( const smtrat::ConstraintT& upper_constr, const smtrat::ConstraintT& lower_Constr, carl::Variable& corr_var );
            
            /*
             * Tries to construct a solution by backtracking through the computation steps
             * and returns whether this was successful
             * * @param temp_solution Contains assignments that have possibly been determined by the backends
             */            
            bool constructSolution( std::map< carl::Variable, Rational > temp_solution ) const;
            
            /*
             * Depending on whether we work on integer or rational instances, it
             * sends the corresponding set of constraints to the backends and returns
             * the answer obtained by the latter
             */
            Answer callBackends();
            
            /*
             * @param  formula_map A map of formulas and their origins
             * @param  new_poly    A polynomial whose formula could be added to formula_map if it is not redundant
             * @return The formula whose polynomial, ignoring the constant part, corresponds
             *         to new_poly. Otherwise, returns a false formula. The second component of the result
             *         indicates whether the formula belonging to new_poly would add new information to formula_map.
             */
            std::pair< FormulaT, bool > worthInserting( FormulaOrigins& formula_map, const Poly& new_poly );
            
        public:
			typedef Settings SettingsType;
std::string moduleName() const {
return SettingsType::moduleName;
}
            FouMoModule( const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager = NULL );

            ~FouMoModule() {}

            /**
             * The module has to take the given sub-formula of the received formula into account.
             *
             * @param _subformula The sub-formula to take additionally into account.
             * @return false, if it can be easily decided that this sub-formula causes a conflict with
             *          the already considered sub-formulas;
             *          true, otherwise.
             */
            bool addCore( ModuleInput::const_iterator _subformula );

            /**
             * Removes the subformula of the received formula at the given position to the considered ones of this module.
             * Note that this includes every stored calculation which depended on this subformula, but should keep the other
             * stored calculation, if possible, untouched.
             *
             * @param _subformula The position of the subformula to remove.
             */
            void removeCore( ModuleInput::const_iterator _subformula );

            /**
             * Updates the current assignment into the model.
             * Note, that this is a unique but possibly symbolic assignment maybe containing newly introduced variables.
             */
            void updateModel() const;

            /**
             * Checks the received formula for consistency.
             * @return SAT,    if the received formula is satisfiable;
             *         UNSAT,   if the received formula is not satisfiable;
             *         Unknown, otherwise.
             */
            Answer checkCore();

    };
}
