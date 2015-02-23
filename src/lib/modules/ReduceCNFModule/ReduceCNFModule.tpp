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
 * @file ReduceCNFModule.tpp
 * @author Dustin Huetter <dustin.huetter@rwth-aachen.de>
 *
 * @version 2015-02-23
 * Created on 2015-02-23.
 */

#include "ReduceCNFModule.h"

namespace smtrat
{
    /**
     * Constructors.
     */

    template<class Settings>
    ReduceCNFModule<Settings>::ReduceCNFModule( ModuleType _type, const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager ):
        Module( _type, _formula, _conditionals, _manager ),
        mVarUpperLower(),
        mTempPassedFormulas()  
    {}

    /**
     * Destructor.
     */

    template<class Settings>
    ReduceCNFModule<Settings>::~ReduceCNFModule()
    {}


    template<class Settings>
    bool ReduceCNFModule<Settings>::inform( const FormulaT& _constraint )
    {
        Module::inform( _constraint ); // This must be invoked at the beginning of this method. 
        const smtrat::ConstraintT* constraint = _constraint.pConstraint(); // Constraint pointer for the passed formula. 
        return constraint->isConsistent() != 0;
    }

    template<class Settings>
    void ReduceCNFModule<Settings>::init()
    {}

    template<class Settings>
    bool ReduceCNFModule<Settings>::assertSubformula( ModuleInput::const_iterator _subformula )
    {
        Module::assertSubformula( _subformula ); // This must be invoked at the beginning of this method.
        // Your code.
        return true; // This should be adapted according to your implementation.
    }

    template<class Settings>
    void ReduceCNFModule<Settings>::removeSubformula( ModuleInput::const_iterator _subformula )
    {
        // Your code.
        Module::removeSubformula( _subformula ); // This must be invoked at the end of this method.
    }

    template<class Settings>
    void ReduceCNFModule<Settings>::updateModel() const
    {
        mModel.clear();
        if( solverState() == True )
        {
            // Your code.
        }
    }

    template<class Settings>
    Answer ReduceCNFModule<Settings>::isConsistent()
    {
        if( !rReceivedFormula().isConstraintConjunction() )
        {
            return foundAnswer( Unknown ); // Unknown
        }
        gather_upper_lower();
        // Check which variables are only bounded in one direction 
        auto iter_vars = mVarUpperLower.begin();
        while( iter_vars != mVarUpperLower.end() )
        {
            if( (*iter_vars).second.first.empty() && !(*iter_vars).second.second.empty() )
            {
                // Replace all 'lower constraints' by TRUE 
                auto iter_constr = (*iter_vars).second.second.begin();
                auto iter_formula = mTempPassedFormulas.find( *iter_constr );
                assert( iter_formula != mTempPassedFormulas.end() );      
            }
            else if( !(*iter_vars).second.first.empty() && (*iter_vars).second.second.empty() )
            {
                // Replace all 'upper constraints' by TRUE    
                auto iter_constr = (*iter_vars).second.first.begin();
                auto iter_formula = mTempPassedFormulas.find( *iter_constr );
                assert( iter_formula != mTempPassedFormulas.end() ); 
            }
            ++iter_vars;
        }
        return Unknown; // This should be adapted according to your implementation.
    }
    
    template<class Settings>
    void ReduceCNFModule<Settings>::gather_upper_lower()
    {
        auto iter_clauses = rReceivedFormula().begin();
        while( iter_clauses != rReceivedFormula().end() )
        {
            auto iter_literals = iter_clauses->formula().begin();
            while( iter_literals != iter_clauses->formula().end() )
            {
                auto iter_terms = iter_literals->constraint().lhs().begin();
                while( iter_terms != iter_literals->constraint().lhs().end() )
                {
                    if( iter_terms->coeff() > 0 )
                    {
                        mVarUpperLower[ iter_terms->getSingleVariable() ].first.push_back( *iter_literals );                        
                    }
                    else
                    {
                        mVarUpperLower[ iter_terms->getSingleVariable() ].second.push_back( *iter_literals );                        
                    }
                    ++iter_terms;
                }
                ++iter_literals;
            }
            ++iter_clauses;
        }
    }
}