/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2013 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT. If not, see <http://www.gnu.org/licenses/>.
 *
 */
/**
 * @file ModuleInput.cpp
 *
 * @author   Florian Corzilius
 * @version: 2014-05-16
 */

#include "ModuleInput.h"

using namespace std;

// Main smtrat namespace.
namespace smtrat
{   
    unsigned ModuleInput::satisfiedBy( const EvalRationalMap& _assignment ) const
    {
        unsigned result = 1;
//        std::cout << __func__ << std::endl;
//        std::cout << "check against " << std::endl; 
//        for( auto iter = _assignment.begin(); iter != _assignment.end(); ++iter )
//            std::cout << iter->first << " -> " << iter->second << std::endl;
        for( auto subFormula = begin(); subFormula != end(); ++subFormula )
        {
//            std::cout << **subFormula << std::endl;
            switch( (*subFormula)->satisfiedBy( _assignment ) )
            {
                case 0:
//                    std::cout << " = false" << std::endl;
                    return 0;
                case 1:
//                    std::cout << " = true" << std::endl;
                    break;
                default:
//                    std::cout << " = unknown" << std::endl;
                    if( result != 2 ) result = 2;
            }
        }
//        std::cout << std::endl << "makes " << result << std::endl << std::endl;
        return result;
    }
    
    void ModuleInput::updateProperties() const
    {
        mProperties = Condition();
        mProperties |= PROP_IS_PURE_CONJUNCTION | PROP_IS_IN_CNF | PROP_IS_IN_NNF;
        mProperties |= PROP_VARIABLE_DEGREE_LESS_THAN_THREE | PROP_VARIABLE_DEGREE_LESS_THAN_FOUR | PROP_VARIABLE_DEGREE_LESS_THAN_FIVE;
        for( auto subFormula = begin(); subFormula != end(); ++subFormula )
        {
            Condition subFormulaConds = (*subFormula)->properties();
            if( !(PROP_IS_A_CLAUSE<=subFormulaConds) )
            {
                mProperties &= ~PROP_IS_PURE_CONJUNCTION;
                mProperties &= ~PROP_IS_IN_CNF;
            }
            else if( !(PROP_IS_A_LITERAL<=subFormulaConds) )
                mProperties &= ~PROP_IS_PURE_CONJUNCTION;
            if( !(PROP_IS_IN_NNF<=subFormulaConds) )
                mProperties &= ~PROP_IS_IN_NNF;
            mProperties |= (subFormulaConds & WEAK_CONDITIONS);
        }
    }
} // namespace smtrat
