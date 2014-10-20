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
 * @file ConstraintPool.cpp
 * @author Florian Corzilius
 * @author Sebastian Junges
 * @author Ulrich Loup
 * @version 2014-10-20
 */

#include "ConstraintPool.h"

using namespace std;

namespace smtrat
{
    ConstraintPool::ConstraintPool( unsigned _capacity ):
        Singleton(),
        mLastConstructedConstraintWasKnown( false ),
        mIdAllocator( 1 ),
        mConsistentConstraint( new Constraint( ZERO_POLYNOMIAL, Relation::EQ, 1 ) ),
        mInconsistentConstraint( new Constraint( ZERO_POLYNOMIAL, Relation::LESS, 2 ) ),
        mConstraints()
    {
        mConstraints.reserve( _capacity );
        mConstraints.insert( mConsistentConstraint );
        mConstraints.insert( mInconsistentConstraint );
        mIdAllocator = 3;
    }

    ConstraintPool::~ConstraintPool()
    {
        mConstraints.erase( mConsistentConstraint );
        delete mConsistentConstraint;
        mConstraints.erase( mInconsistentConstraint );
        delete mInconsistentConstraint;
        while( !mConstraints.empty() )
        {
            const Constraint* pCons = (*mConstraints.begin());
            mConstraints.erase( mConstraints.begin() );
            delete pCons;
        }
    }

    void ConstraintPool::clear()
    {
        CONSTRAINT_POOL_LOCK_GUARD
        mConstraints.erase( mConsistentConstraint );
        mConstraints.erase( mInconsistentConstraint );
        while( !mConstraints.empty() )
        {
            const Constraint* pCons = (*mConstraints.begin());
            mConstraints.erase( mConstraints.begin() );
            delete pCons;
        }
        mConstraints.insert( mConsistentConstraint );
        mConstraints.insert( mInconsistentConstraint );
        mIdAllocator = 3;
    }
    
    const Constraint* ConstraintPool::newBound( const carl::Variable& _var, const Relation _rel, const Rational& _bound )
    {
        CONSTRAINT_POOL_LOCK_GUARD
        // TODO: Maybe it's better to increment the allocator even if the constraint already exists.
        //       Avoids long waiting for access (mutual exclusion) but increases the allocator to fast.
        Constraint* constraint = createNormalizedBound( _var, _rel, _bound );
        auto iterBoolPair = mConstraints.insert( constraint );
        if( iterBoolPair.second )
            mLastConstructedConstraintWasKnown = false;
        else
        {
            mLastConstructedConstraintWasKnown = true;
            delete constraint;
        }
        return *iterBoolPair.first;
    }

    const Constraint* ConstraintPool::newConstraint( const Polynomial& _lhs, const Relation _rel )
    {
        CONSTRAINT_POOL_LOCK_GUARD
        // TODO: Maybe it's better to increment the allocator even if the constraint already exists.
        //       Avoids long waiting for access (mutual exclusion) but increases the allocator to fast.
//        cout << "create polynomial  " << _lhs << " " << Constraint::relationToString( _rel ) << "0" << endl;
        Constraint* constraint = createNormalizedConstraint( _lhs, _rel );
//        cout << "   " << *constraint << endl;
        if( constraint->variables().empty() )
        {
            bool constraintConsistent = Constraint::evaluate( constraint->constantPart(), constraint->relation() );
            delete constraint;
            return ( constraintConsistent ? mConsistentConstraint : mInconsistentConstraint );
        }
        const Constraint* result = addConstraintToPool( constraint );
        return result;
    }

    Constraint* ConstraintPool::createNormalizedBound( const carl::Variable& _var, const Relation _rel, const Rational& _bound ) const
    {
        assert( _rel != Relation::EQ && _rel != Relation::NEQ );
        if( _rel == Relation::GREATER )
        {
            Polynomial lhs = Polynomial( _bound ) - Polynomial( _var );
            return new Constraint( lhs, Relation::LESS, mIdAllocator );
        }
        else if( _rel == Relation::GEQ )
        {
            Polynomial lhs = Polynomial( _bound ) - Polynomial( _var );
            return new Constraint( lhs, Relation::LEQ, mIdAllocator );
        }
        else
        {
            Polynomial lhs = Polynomial( _var ) - Polynomial( _bound );
            return new Constraint( lhs, _rel, mIdAllocator );
        }
    }
    
    Constraint* ConstraintPool::createNormalizedConstraint( const Polynomial& _lhs, const Relation _rel ) const
    {
        if( _rel == Relation::GREATER )
        {
            Polynomial lhs = _lhs.isZero() ? ZERO_POLYNOMIAL : _lhs.coprimeCoefficients();
            if( !lhs.isZero() && (_lhs.lterm()->coeff() < 0) == (lhs.lterm()->coeff() < 0) )
            {
                lhs = -lhs;
            }
            return new Constraint( lhs, Relation::LESS );
        }
        else if( _rel == Relation::GEQ )
        {
            Polynomial lhs = _lhs.isZero() ? ZERO_POLYNOMIAL : _lhs.coprimeCoefficients();
            if( !lhs.isZero() && (_lhs.lterm()->coeff() < 0) == (lhs.lterm()->coeff() < 0) )
            {
                lhs = -lhs;
            }
            return new Constraint( lhs, Relation::LEQ );
        }
        else
        {
            Polynomial lhs = _lhs.isZero() ? ZERO_POLYNOMIAL : _lhs.coprimeCoefficients();
            if( _rel == Relation::EQ || _rel == Relation::NEQ ) 
            {
                if( !_lhs.isZero() && lhs.lterm()->coeff() < ZERO_RATIONAL ) lhs = -lhs;
            }
            else if( !lhs.isZero() && (_lhs.lterm()->coeff() < 0) != (lhs.lterm()->coeff() < 0) )
            {
                lhs = -lhs;
            }
            return new Constraint( lhs, _rel );
        }
    }

    const Constraint* ConstraintPool::addConstraintToPool( Constraint* _constraint )
    {
        mLastConstructedConstraintWasKnown = false;
        unsigned constraintConsistent = _constraint->isConsistent();
//        cout << *_constraint << " is consistent: " << constraintConsistent << endl;
		///@todo Use appropriate constant instead of 2.
        if( constraintConsistent == 2 ) // Constraint contains variables.
        {
            auto iterBoolPair = mConstraints.insert( _constraint );
            if( !iterBoolPair.second ) // Constraint has already been generated.
            {
                mLastConstructedConstraintWasKnown = true;
                delete _constraint;
            }
            else
            {
                Constraint* constraint = _constraint->simplify();
                if( constraint != NULL ) // Constraint could be simplified.
                {
//                    cout << *_constraint << " can be simplified to " << *constraint << endl;
                    mConstraints.erase( iterBoolPair.first );
                    delete _constraint;
                    auto iterBoolPairB = mConstraints.insert( constraint );
                    if( !iterBoolPairB.second ) // Simplified version already exists
                    {
                        mLastConstructedConstraintWasKnown = true;
                        delete constraint;
                    }
                    else // Simplified version has not been generated before.
                    {
                        constraint->init();
                        constraint->mID = mIdAllocator;
                        ++mIdAllocator;
                    }
                    return *iterBoolPairB.first;
                }
                else // Constraint could not be simplified.
                {
                    _constraint->mID = mIdAllocator;
                    ++mIdAllocator;
                }
            }
            return *iterBoolPair.first;
        }
        else // Constraint contains no variables.
        {
            mLastConstructedConstraintWasKnown = true;
            delete _constraint;
            return (constraintConsistent ? mConsistentConstraint : mInconsistentConstraint );
        }
    }

    void ConstraintPool::print( ostream& _out ) const
    {
        CONSTRAINT_POOL_LOCK_GUARD
        _out << "Constraint pool:" << endl;
        for( auto constraint = mConstraints.begin(); constraint != mConstraints.end(); ++constraint )
            _out << "    " << **constraint << "  [id=" << (*constraint)->id() << ", hash=" << (*constraint)->getHash() << "]" << endl;
        _out << "---------------------------------------------------" << endl;
    }
    
    const Constraint* newBound( const carl::Variable& _var, const Relation _rel, const Rational& _bound )
    {
        return ConstraintPool::getInstance().newBound( _var, _rel, _bound );
    }

    const Constraint* newConstraint( const Polynomial& _lhs, const Relation _rel )
    {
        return ConstraintPool::getInstance().newConstraint( _lhs, _rel );
    }

    const ConstraintPool& constraintPool()
    {
        return ConstraintPool::getInstance();
    }
}    // namespace smtrat

