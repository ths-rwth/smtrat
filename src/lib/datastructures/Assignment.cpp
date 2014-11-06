/*
 *  SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
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
 * Class to create a state object.
 * @author Florian Corzilius
 * @since 2014-01-14
 * @version 2014-01-14
 */

#include "Assignment.h"

namespace smtrat
{
    bool getRationalAssignmentsFromModel( const Model& _model, EvalRationalMap& _rationalAssigns )
    {
        bool result = true;
        for( auto ass = _model.begin(); ass != _model.end(); ++ass )
        {   
            if (ass->first.getType() == carl::VariableType::VT_BOOL)
            {
                _rationalAssigns.insert( _rationalAssigns.end(), std::make_pair( ass->first, (ass->second.asBool() ? ONE_RATIONAL : ZERO_RATIONAL) ) );
            }
            else if (ass->second.isSqrtEx())
            {
                if( ass->second.asSqrtEx().isConstant() && !ass->second.asSqrtEx().hasSqrt() )
                {
                    Rational value = ass->second.asSqrtEx().constantPart().constantPart()/ass->second.asSqrtEx().denominator().constantPart();
                    assert( !(ass->first.getType() == carl::VariableType::VT_INT) || carl::isInteger( value ) );
                    _rationalAssigns.insert( _rationalAssigns.end(), std::make_pair(ass->first, value));
                }
                else
                {
                    result = false;
                }
            }
            else if (ass->second.isRAN())
            {
                if (ass->second.asRAN()->isNumeric())
                {
                    _rationalAssigns.insert( _rationalAssigns.end(), std::make_pair(ass->first, ass->second.asRAN()->value()) );
                }
            }
        }
        return result;
    }
    
    unsigned satisfies( const Model& _assignment, const FormulaT* _formula )
    {
        EvalRationalMap rationalAssigns;
        if( getRationalAssignmentsFromModel( _assignment, rationalAssigns ) )
            return _formula->satisfiedBy( rationalAssigns );
        else
            return 2; // TODO: Check also models having square roots as value.
    }
}    
