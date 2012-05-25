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
 * Class to create a condition object.
 * @author Florian Corzilius
 * @since 2010-07-26
 * @version 2011-12-05
 */

#include "Condition.h"

namespace vs
{
    /**
     * Constructors:
     */
    Condition::Condition()
    {
        mpConstraint         = new smtrat::Constraint();
        mFlag                = false;
        mRecentlyAdded       = false;
        mpOriginalConditions = new ConditionSet();
        mValuation           = 0;
    }

    Condition::Condition( const smtrat::Constraint& _constraint )
    {
        mpConstraint         = new smtrat::Constraint( _constraint );
        mFlag                = false;
        mRecentlyAdded       = false;
        mpOriginalConditions = new ConditionSet();
        mValuation           = 0;
    }

    Condition::Condition( const smtrat::Constraint& _constraint, const unsigned _valuation )
    {
        mpConstraint         = new smtrat::Constraint( _constraint );
        mFlag                = false;
        mRecentlyAdded       = false;
        mpOriginalConditions = new ConditionSet();
        mValuation           = _valuation;
    }

    Condition::Condition( const smtrat::Constraint& _constraint,
                          const bool _flag,
                          const ConditionSet& _originalConditions,
                          const unsigned _valuation )
    {
        mpConstraint         = new smtrat::Constraint( _constraint );
        mFlag                = _flag;
        mRecentlyAdded       = false;
        mpOriginalConditions = new ConditionSet( _originalConditions );
        mValuation           = _valuation;
    }

    Condition::Condition( const smtrat::Constraint& _constraint,
                          const bool _flag,
                          const ConditionSet& _originalConditions,
                          const unsigned _valuation,
                          const bool _recentlyAdded )
    {
        mpConstraint         = new smtrat::Constraint( _constraint );
        mFlag                = _flag;
        mRecentlyAdded       = _recentlyAdded;
        mpOriginalConditions = new ConditionSet( _originalConditions );
        mValuation           = _valuation;
    }

    Condition::Condition( const Condition& _condition )
    {
        mpConstraint         = new smtrat::Constraint( _condition.constraint() );
        mFlag                = _condition.flag();
        mRecentlyAdded       = false;
        mpOriginalConditions = new ConditionSet( _condition.originalConditions() );
        mValuation           = _condition.valuation();
    }

    /**
     * Destructor:
     */
    Condition::~Condition()
    {
        delete mpConstraint;
        (*mpOriginalConditions).clear();
        delete mpOriginalConditions;
    }

    /**
     * Methods:
     */

    /**
     * Checks the equality of a given condition (right hand side) with this condition (left hand side).
     *
     * @param _condition The condition to compare with (rhs).
     *
     * @return  true    ,if the given condition is equal to this condition;
     *          false   ,otherwise.
     */
    bool Condition::operator ==( const Condition& _condition ) const
    {
        if( valuation() == _condition.valuation() )
        {
            return true;
        }
        else
        {
            return false;
        }
    }

    /**
     * Checks if the given condition (right hand side) is greater than this condition (left hand side).
     *
     * @param _condition The condition to compare with (rhs).
     *
     * @return  true    ,if the given substitution is greater than this substitution;
     *          false   ,otherwise.
     */
    bool Condition::operator <( const Condition& _condition ) const
    {
        if( valuation() < _condition.valuation() )
        {
            return true;
        }
        else
        {
            return false;
        }
    }

    /**
     * Prints the condition to an output stream.
     *
     * @param _out The output stream, where it should print.
     */
    void Condition::print( std::ostream& _out ) const
    {
        constraint().print( _out );
        _out << " [" << this << "]";
        _out << "   ";
        if( flag() )
        {
            _out << "(true, ";
        }
        else
        {
            _out << "(false, ";
        }
        _out << "valuation=" << valuation();
        if( recentlyAdded() )
        {
            _out << ", recently added) {";
        }
        else
        {
            _out << ") {";
        }
        if( originalConditions().empty() )
        {
            _out << "no original condition}";
        }
        else
        {
            ConditionSet::const_iterator oCond = originalConditions().begin();
            _out << " [" << *oCond << "]";
            oCond++;
            while( oCond != originalConditions().end() )
            {
                _out << ", [" << *oCond << "]";
                oCond++;
            }
            _out << " }";
        }
    }

}    // end namspace vs

