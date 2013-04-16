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
/*
 * File:   ReduceModule.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version DATE
 * Created on DATE.
 */

#include "ReduceModule.h"

namespace smtrat
{
    /**
     * Constructors.
     */

    ReduceModule::ReduceModule( ModuleType _type, const Formula* const _formula, RuntimeSettings* settings, Conditionals& _conditionals, Manager* const _manager ):
        Module( _type, _formula, _conditionals, _manager )
    {
    }

    /**
     * Destructor.
     */

    ReduceModule::~ReduceModule()
    {
    }

    /**
     * Main interfaces.
     */

    /**
     * Informs this module about the existence of the given constraint, which means
     * that it could be added in the future.
     *
     * @param _constraint The constraint to inform about.
     * @return False, if the it can be determined that the constraint itself is conflicting;
     *          True,  otherwise.
     */
    bool ReduceModule::inform( const Constraint* const _constraint )
    {
        Module::inform( _constraint ); // This must be invoked at the beginning of this method.
        // Your code.
        return _constraint->isConsistent() != 0;
    }

    /**
     * Add the subformula of the received formula at the given position to the considered ones of this module.
     *
     * @param _subformula The position of the subformula to add.
     * @return False, if it is easy to decide whether the subformula at the given position is unsatisfiable;
     *          True,  otherwise.
     */
    bool ReduceModule::assertSubformula( Formula::const_iterator _subformula )
    {
        Module::assertSubformula( _subformula ); // This must be invoked at the beginning of this method.
        // Your code.
        return true; // This should be adapted according to your implementation.
    }

    /**
     * Removes the subformula of the received formula at the given position to the considered ones of this module.
     * Note that this includes every stored calculation which depended on this subformula.
     *
     * @param _subformula The position of the subformula to remove.
     */
    void ReduceModule::removeSubformula( Formula::const_iterator _subformula )
    {
        // Your code.
        Module::removeSubformula( _subformula ); // This must be invoked at the end of this method.
    }

    /**
     * Updates the current assignment into the model.
     * Note, that this is a unique but possibly symbolic assignment maybe containing newly introduced variables.
     */
    void ReduceModule::updateModel()
    {
        mModel.clear();
        if( solverState() == True )
        {
            // Your code.
        }
    }

    /**
     * Checks the received formula for consistency.
     */
    Answer ReduceModule::isConsistent()
    {
        // Your code.
        return Unknown; // This should be adapted according to your implementation.
    }
}