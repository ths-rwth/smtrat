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
 * @file IntEqModule.h
 * @author Dustin Huetter <dustin.huetter@rwth-aachen.de>
 *
 * @version 2014-10-17
 * Created on 2014-10-17.
 */
#pragma once
#include "../../solver/Module.h"
#include "IntEqStatistics.h"
#include "IntEqSettings.h"
#include <stdio.h>
namespace smtrat
{
    typedef std::map<FormulaT,vector<std::set<FormulaT>>> FormulaOrigins;
        
    /**
     * A module which checks whether the equations contained in the received formula 
     * have an integer solution.
     */    
    template<typename Settings>
    class IntEqModule : public Module
    {
        private:
            // Stores the equations of the received constraints and their origins
            FormulaOrigins mProc_Constraints; 
            // Stores the calculated substitutions
            std::map<carl::Variable, Poly>  mSubstitutions;
            // Stores the origins of the calculated substitutions
            std::map<carl::Variable, vector<std::set<FormulaT>>> mVariables;
            
        public:
            IntEqModule( ModuleType _type, const ModuleInput* _formula, RuntimeSettings* _settings, Conditionals& _conditionals, Manager* _manager = NULL );
            ~IntEqModule();
            // Main interfaces.
            /**
             * Informs the module about the given constraint. It should be tried to inform this
             * module about any constraint it could receive eventually before assertSubformula
             * is called (preferably for the first time, but at least before adding a formula
             * containing that constraint).
             * @param _constraint The constraint to inform about.
             * @return false, if it can be easily decided whether the given constraint is inconsistent;
             *          true, otherwise.
             */
            bool inform( const FormulaT& _constraint );
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
             *          the already considered sub-formulas;
             *          true, otherwise.
             */
            bool assertSubformula( ModuleInput::const_iterator _subformula );
            /**
             * Removes the subformula of the received formula at the given position to the considered ones of this module.
             * Note that this includes every stored calculation which depended on this subformula, but should keep the other
             * stored calculation, if possible, untouched.
             *
             * @param _subformula The position of the subformula to remove.
             */
            void removeSubformula( ModuleInput::const_iterator _subformula );
            /**
             * Updates the current assignment into the model.
             * Note, that this is a unique but possibly symbolic assignment maybe containing newly introduced variables.
             */
            void updateModel() const;
            /**
             * Checks the received formula for consistency.
             * @return True,    if the received formula is satisfiable;
             *         False,   if the received formula is not satisfiable;
             *         Unknown, otherwise.
             */
            Answer isConsistent();
    };
}
#include "IntEqModule.tpp"
