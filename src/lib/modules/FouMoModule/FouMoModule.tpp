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
 * @file FouMoModule.tpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2014-12-01
 * Created on 2014-12-01.
 */

#include "FouMoModule.h"

namespace smtrat
{
    /**
     * Constructors.
     */

    template<class Settings>
    FouMoModule<Settings>::FouMoModule( ModuleType _type, const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager ):
        Module( _type, _formula, _conditionals, _manager ) 
    {}

    /**
     * Destructor.
     */

    template<class Settings>
    FouMoModule<Settings>::~FouMoModule()
    {}


    template<class Settings>
    bool FouMoModule<Settings>::inform( const FormulaT& _constraint )
    {
        Module::inform( _constraint ); // This must be invoked at the beginning of this method.
        // Your code.
        const smtrat::ConstraintT* constraint = _constraint.pConstraint();
        return constraint->isConsistent() != 0;
    }

    template<class Settings>
    void FouMoModule<Settings>::init()
    {}

    template<class Settings>
    bool FouMoModule<Settings>::assertSubformula( ModuleInput::const_iterator _subformula )
    {
        Module::assertSubformula( _subformula ); // This must be invoked at the beginning of this method.
        // Your code.
        return true; // This should be adapted according to your implementation.
    }

    template<class Settings>
    void FouMoModule<Settings>::removeSubformula( ModuleInput::const_iterator _subformula )
    {
        // Your code.
        Module::removeSubformula( _subformula ); // This must be invoked at the end of this method.
    }

    template<class Settings>
    void FouMoModule<Settings>::updateModel() const
    {
        mModel.clear();
        if( solverState() == True )
        {
            // Your code.
        }
    }

    template<class Settings>
    Answer FouMoModule<Settings>::isConsistent()
    {
        // Your code.
        return Unknown; // This should be adapted according to your implementation.
    }
}