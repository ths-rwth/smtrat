/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
 *
 * This file is part of SMT-RAT.
 *
 * SMT-RAT is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMT-RAT is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *
 */
/**
 * @file FouMoModule.h
 * @author Dustin Huetter <dustin.huetter@rwth-aachen.de>
 *
 * @version 2014-12-01
 * Created on 2014-12-01.
 */

#pragma once

#include "../../solver/Module.h"
#include "FouMoStatistics.h"
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
            // Stores the equalities
            FormulaOrigins mEqualities;
            // Stores the disequalities
            FormulaOrigins mDisequalities;
            // Stores the order in which the variables were eliminated
            std::vector<carl::Variable> mElim_Order;
            // Stores the deleted constraints, just as they worked as an upper respectively lower
            // bound when eliminating the corresponding variable. The variables and their corresponding
            // upper/lower constraints are saved in the order given by mElim_Order
            VariableUpperLower mDeleted_Constraints;  
            // Stores constructed assignments for the occuring variables when a solution was found
            std::map<carl::Variable, Rational> mVarAss;
            // Stores whether we found a valid solution in this module
            bool mCorrect_Solution;
            
            /**
             * @param curr_constraints Contains the constraints for which a possibly good
             *                         variable is chosen
             * @param var_corr_constr  Contains the chosen variable and the constraints for the elimination step
             */
            void gather_upper_lower( FormulaOrigins& curr_constraints, VariableUpperLower& var_corr_constr );
            
            /**
             * @param upper_constr Pointer to the constraint corresponding to an upper bound of corr_var          *                         variable is chosen
             * @param lower_constr Pointer to the constraint corresponding to a lower bound of corr_var
             * @param corr_var     Variable that shall be eliminated
             * @return             Pointer to the constraint resulting from the combination
             */
            FormulaT combine_upper_lower( const smtrat::ConstraintT& upper_constr, const smtrat::ConstraintT& lower_Constr, carl::Variable& corr_var );
            
            /*
             * Tries to construct a solution by backtracking through the computation steps
             * and returns whether this was successful
             */            
            bool construct_solution();
            
            /*
             * Depending on whether we work on integer or rational instances, it
             * sends the corresponding set of constraints to the backends and returns
             * the answer obtained by the backends
             */
            Answer call_backends( bool _full );
            
            /*
             * Resets all data structures of this module to the initial assignments
             */
            void fresh_start();
            
        public:
            FouMoModule( ModuleType _type, const ModuleInput* _formula, RuntimeSettings* _settings, Conditionals& _conditionals, Manager* _manager = NULL );

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
             * @param _full false, if this module should avoid too expensive procedures and rather return unknown instead.
             * @return True,    if the received formula is satisfiable;
             *         False,   if the received formula is not satisfiable;
             *         Unknown, otherwise.
             */
            Answer checkCore( bool _full );

    };
}

#include "FouMoModule.tpp"
