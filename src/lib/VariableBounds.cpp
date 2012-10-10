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
 * @file VariableBounds.cpp
 * @author Florian Corzilius
 * @since 2012-10-04
 * @version 2012-10-04
 */

#include "VariableBounds.h"
#include "modules/FourierMotzkinSimplifier.h"

using namespace std;
using namespace GiNaC;
using namespace GiNaCRA;

namespace smtrat
{
    /**
     * Constructor for a bound.
     *
     * @param _limit A pointer to the limit (rational) of the bound. It is NULL, if the limit is not finite.
     * @param _variable The variable to which this bound belongs.
     * @param _type The type of the bound (either it is an equal bound or it is weak resp. strict and upper resp. lower)
     */
    VariableBounds::Bound::Bound( numeric* const _limit, Variable* const _variable, Type _type ):
        mType( _type ),
        mpLimit( _limit ),
        mpVariable( _variable ),
        mpInfo( new Info() )
    {
        mpInfo->activity = 1;
    }

    /**
     * Destructor for a bound.
     */
    VariableBounds::Bound::~Bound()
    {
        delete mpInfo;
        delete mpLimit;
    }

    /**
     * Checks whether the this bound is smaller than the given one.
     *
     * @param _bound
     * @return True,    if for this bound (A) and the given bound (B) it holds that:
     *
     *                      A is not inf   and   B is inf,
     *                      A smaller than B, where A and B are rationals,
     *                      A equals B, where A and B are rationals, but A is an equal bound but B is not;
     *         False,   otherwise.
     */
    bool VariableBounds::Bound::operator <( const Bound& _bound ) const
    {
        if( mpLimit == NULL && _bound.pLimit() == NULL )
        {
            return (mType == STRICT_LOWER_BOUND && _bound.type() == STRICT_UPPER_BOUND );
        }
        else if( mpLimit == NULL && _bound.pLimit() != NULL )
        {
            return mType == STRICT_LOWER_BOUND;
        }
        else if( mpLimit != NULL && _bound.pLimit() == NULL )
        {
            return _bound.type() == STRICT_UPPER_BOUND;
        }
        else
        {
            if( *mpLimit < _bound.limit() )
            {
                return true;
            }
            else if( *mpLimit == _bound.limit() )
            {
                if( mType == EQUAL_BOUND && _bound.type() != EQUAL_BOUND ) return true;
            }
            return false;
        }
    }

    /**
     * Prints the bound on the given output stream.
     *
     * @param _ostream The output stream to print on.
     * @param _bound The bound to print.
     * @return The output stream after printing the bound on it.
     */
    ostream& operator <<( ostream& _ostream, const VariableBounds::Bound& _bound )
    {
        if( _bound.isInfinite() )
        {
            if( _bound.type() == VariableBounds::Bound::STRICT_LOWER_BOUND )
            {
                _ostream << "-inf";
            }
            else
            {
                _ostream << "inf";
            }
        }
        else
        {
            _ostream << _bound.limit();
        }
        return _ostream;
    }

    /**
     * Constructor of a variable.
     */
    VariableBounds::Variable::Variable():
        mUpdated( true ),
        mUpperbounds( BoundSet() ),
        mLowerbounds( BoundSet() )
    {
        mUpperbounds.insert( new Bound( NULL, this, Bound::STRICT_UPPER_BOUND ) );
        mpSupremum = *mUpperbounds.begin();
        mLowerbounds.insert( new Bound( NULL, this, Bound::STRICT_LOWER_BOUND ) );
        mpInfimum = *mLowerbounds.begin();
    }

    /**
     * Destructor of a variable.
     */
    VariableBounds::Variable::~Variable()
    {
        while( !mLowerbounds.empty() )
        {
            const Bound* toDelete = *mLowerbounds.begin();
            mLowerbounds.erase( mLowerbounds.begin() );
            if( !toDelete->type() == Bound::EQUAL_BOUND ) delete toDelete;
        }
        while( !mUpperbounds.empty() )
        {
            const Bound* toDelete = *mUpperbounds.begin();
            mUpperbounds.erase( mUpperbounds.begin() );
            delete toDelete;
        }
    }

    /**
     * Adds the bound corresponding to the constraint to the given variable. The constraint
     * is expected to contain only one variable and this one only linearly.
     *
     * @param _constraint A constraint of the form ax~b.
     * @param _var Hence, the variable x.
     * @return The added bound.
     */
    const VariableBounds::Bound* VariableBounds::Variable::addBound( const Constraint* _constraint, const ex& _var )
    {
        assert( _constraint->variables().size() == 1 && _constraint->lhs().degree( _var ) == 1 );
        numeric coeff = ex_to<numeric>( _constraint->lhs().coeff( _var, 1 ) );
        Constraint_Relation rel = _constraint->relation();
        numeric* limit = new numeric( -_constraint->constantPart()/coeff );
        pair<BoundSet::iterator, bool> result;
        if( rel == CR_EQ )
        {
            Bound* newBound = new Bound( limit, this, Bound::EQUAL_BOUND );
            result = mUpperbounds.insert( newBound );
            if( !result.second )
            {
                delete newBound;
            }
            else
            {
                mLowerbounds.insert( newBound );
            }
        }
        else if( ( rel == CR_GEQ && coeff < 0 ) || ( rel == CR_LEQ && coeff > 0 ) )
        {
            Bound* newBound = new Bound( limit, this, Bound::WEAK_UPPER_BOUND );
            result = mUpperbounds.insert( newBound );
            if( !result.second )
            {
                delete newBound;
            }
        }
        else if( ( rel == CR_LEQ && coeff < 0 ) || ( rel == CR_GEQ && coeff > 0 ) )
        {
            Bound* newBound = new Bound( limit, this, Bound::WEAK_LOWER_BOUND );
            result = mLowerbounds.insert( newBound );
            if( !result.second )
            {
                delete newBound;
            }
        }
        else if( ( rel == CR_GREATER && coeff < 0 ) || ( rel == CR_LESS && coeff > 0 ) )
        {
            Bound* newBound = new Bound( limit, this, Bound::STRICT_UPPER_BOUND );
            result = mUpperbounds.insert( newBound );
            if( !result.second )
            {
                delete newBound;
            }
        }
        else if( ( rel == CR_LESS && coeff < 0 ) || ( rel == CR_GREATER && coeff > 0 ) )
        {
            Bound* newBound = new Bound( limit, this, Bound::STRICT_LOWER_BOUND );
            result = mLowerbounds.insert( newBound );
            if( !result.second )
            {
                delete newBound;
            }
        }
        else
        {
            assert( false );
        }
        return *result.first;
    }

    /**
     * Updates the infimum and supremum of this variable.
     *
     * @param _changedBound The bound, for which we certainly know that it got deactivated before.
     */
    void VariableBounds::Variable::updateBounds( const Bound& _changedBound )
    {
        mUpdated = true;
        if( _changedBound.isUpperBound() )
        {
            // Update the supremum.
            BoundSet::iterator newBound = mUpperbounds.begin();
            while( newBound != mUpperbounds.end() )
            {
                if( (*newBound)->isActive() )
                {
                    mpSupremum = *newBound;
                    break;
                }
                ++newBound;
            }
        }
        if( _changedBound.isLowerBound() )
        {
            // Update the infimum.
            BoundSet::reverse_iterator newBound = mLowerbounds.rbegin();
            while( newBound != mLowerbounds.rend() )
            {
                if( (*newBound)->isActive() )
                {
                    mpInfimum = *newBound;
                    break;
                }
                ++newBound;
            }
        }
    }

    /**
     * Constructor for the variable bounds.
     */
    VariableBounds::VariableBounds():
        mBoundsChanged( false ),
        mpExVariableMap( new ExVariableMap() ),
        mpConstraintBoundMap( new ConstraintBoundMap() ),
        mEvalIntervalMap()
    {}

    /**
     * Destructor for the variable bounds.
     */
    VariableBounds::~VariableBounds()
    {
        mpConstraintBoundMap->clear();
        delete mpConstraintBoundMap;
        while( !mpExVariableMap->empty() )
        {
            Variable* toDelete = mpExVariableMap->begin()->second;
            mpExVariableMap->erase( mpExVariableMap->begin() );
            delete toDelete;
        }
    }

    /**
     * Updates the variable bounds by the given constraint.
     *
     * @param The constraint to consider.
     * @return True, if the variable bounds had been changed;
     *         False, otherwise.
     */
    bool VariableBounds::addBound( const Constraint* _constraint )
    {
        if( _constraint->variables().size() == 1 )
        {
            ex* var = new ex( _constraint->variables().begin()->second );
            if( _constraint->lhs().degree( *var ) == 1 )
            {
                ConstraintBoundMap::iterator cbPair = mpConstraintBoundMap->find( _constraint );
                if( cbPair != mpConstraintBoundMap->end() )
                {
                    const Bound& bound = *cbPair->second;
                    if( bound.activate() ) bound.pVariable()->updateBounds( bound );
                }
                else
                {
                    Variable* variable;
                    const Bound* bound;
                    ExVariableMap::iterator evPair = mpExVariableMap->find( var );
                    if( evPair != mpExVariableMap->end() )
                    {
                        delete var;
                        variable = evPair->second;
                        bound = variable->addBound( _constraint, *evPair->first );
                    }
                    else
                    {
                        variable = new Variable();
                        (*mpExVariableMap)[var] = variable;
                        bound = variable->addBound( _constraint, *var );
                    }
                    mpConstraintBoundMap->insert( pair< const Constraint*, const Bound* >( _constraint, bound ) );
                    variable->updateBounds( *bound );
                }
                return true;
            }
            else
            {
                mpExVariableMap->insert( pair< const ex*, Variable* >( var, new Variable() ) );
            }
        }
        else
        {
            for( auto sym = _constraint->variables().begin(); sym !=  _constraint->variables().end(); ++sym )
            {
                ex* var = new ex( sym->second );
                mpExVariableMap->insert( pair< const ex*, Variable* >( var, new Variable() ) );
            }
        }
        return false;
    }

    /**
     * Removes all effects the given constraints has on the variable bounds.
     *
     * @param The constraints, which effects shall be undone for the variable bounds.
     * @return A variable, if its bounds has been changed;
     *         0         , otherwise.
     */
    const ex VariableBounds::removeBound( const Constraint* _constraint )
    {
        if( _constraint->variables().size() == 1 )
        {
            const ex var = _constraint->variables().begin()->second;
            if( _constraint->lhs().degree( var ) == 1 )
            {
                assert( mpConstraintBoundMap->find( _constraint ) != mpConstraintBoundMap->end() );
                const Bound& bound = *(*mpConstraintBoundMap)[_constraint];
                if( bound.deactivate() )
                {
                    bound.pVariable()->updateBounds( bound );
                    return var;
                }
            }
        }
        return 0;
    }

    /**
     * Creates an evalintervalmap corresponding to the variable bounds.
     *
     * @return The variable bounds as an evalintervalmap.
     */
    const evalintervalmap& VariableBounds::getEvalIntervalMap()
    {
        for( auto exVarPair = mpExVariableMap->begin(); exVarPair != mpExVariableMap->end(); ++exVarPair )
        {
            Variable& var = *exVarPair->second;
            if( var.updated() )
            {
                Interval::BoundType lowerBoundType;
                numeric lowerBoundValue;
                Interval::BoundType upperBoundType;
                numeric upperBoundValue;
                if( var.infimum().isInfinite() )
                {
                    lowerBoundType = Interval::INFINITY_BOUND;
                    lowerBoundValue = 0;
                }
                else
                {
                    lowerBoundType = var.infimum().type() != Bound::WEAK_UPPER_BOUND ? Interval::STRICT_BOUND : Interval::WEAK_BOUND;
                    lowerBoundValue = var.infimum().limit();
                }
                if( var.supremum().isInfinite() )
                {
                    upperBoundType = Interval::INFINITY_BOUND;
                    upperBoundValue = 0;
                }
                else
                {
                    upperBoundType = var.supremum().type() != Bound::WEAK_UPPER_BOUND ? Interval::STRICT_BOUND : Interval::WEAK_BOUND;
                    upperBoundValue = var.supremum().limit();
                }
                mEvalIntervalMap[ex_to<symbol>( *exVarPair->first )] = Interval( lowerBoundValue, lowerBoundType, upperBoundValue, upperBoundType );
                var.hasBeenUpdated();
            }
        }
        return mEvalIntervalMap;
    }

    /**
     * Prints the variable bounds.
     *
     * @param _out The output stream to print on.
     */
    void VariableBounds::print( ostream& _out, const string _init ) const
    {
        for( auto exVarPair = mpExVariableMap->begin(); exVarPair != mpExVariableMap->end(); ++exVarPair )
        {
            _out << _init;
            stringstream outA;
            outA << *exVarPair->first;
            _out << setw( 15 ) << outA.str();
            _out << "  in  ";
            if( exVarPair->second->infimum().type() == Bound::STRICT_LOWER_BOUND )
            {
                _out << "] ";
            }
            else
            {
                _out << "[ ";
            }
            stringstream outB;
            outB << exVarPair->second->infimum();
            _out << setw( 12 ) << outB.str();
            _out << ", ";
            stringstream outC;
            outC << exVarPair->second->supremum();
            _out << setw( 12 ) << outC.str();
            if( exVarPair->second->supremum().type() == Bound::STRICT_UPPER_BOUND )
            {
                _out << " [";
            }
            else
            {
                _out << " ]";
            }
            _out << endl;
        }
    }
}    // namespace smtrat