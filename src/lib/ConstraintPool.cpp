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
 *
 * @author Florian Corzilius
 * @author Sebastian Junges
 * @author Ulrich Loup
 * @version 2013-10-21
 */

#include "ConstraintPool.h"

using namespace std;

namespace smtrat
{
    ConstraintPool::ConstraintPool( unsigned _capacity ):
        mExternalPrefixInitialized( true ),
        mIdAllocator( 1 ),
        mAuxiliaryBoolVarCounter( 0 ),
        mAuxiliaryRealVarCounter( 0 ),
        mAuxiliaryIntVarCounter( 0 ),
        mConsistentConstraint( new Constraint( ZERO_POLYNOMIAL, Constraint::EQ, 1 ) ),
        mInconsistentConstraint( new Constraint( ZERO_POLYNOMIAL, Constraint::LESS, 2 ) ),
        mExternalVarNamePrefix( "_" ),
        mExternalNamesToVariables(),
        mBooleanVariables(),
        mConstraints(),
        mVariablePool( carl::VariablePool::getInstance() )
    {
        mConstraints.reserve( _capacity );
        mConstraints.insert( mConsistentConstraint );
        mConstraints.insert( mInconsistentConstraint );
        mIdAllocator = 3;
    }

    /**
     * Destructor of the constraint pool.
     */
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
        lock_guard<mutex> lock1( mMutexArithmeticVariables );
        lock_guard<mutex> lock2( mMutexBooleanVariables );
        lock_guard<mutex> lock3( mMutexDomain );
        CONSTRAINT_LOCK_GUARD
        mConstraints.erase( mConsistentConstraint );
        mConstraints.erase( mInconsistentConstraint );
        while( !mConstraints.empty() )
        {
            const Constraint* pCons = (*mConstraints.begin());
            mConstraints.erase( mConstraints.begin() );
            delete pCons;
        }
        mAuxiliaryRealVarCounter = 0;
        mAuxiliaryIntVarCounter = 0;
        while( !mBooleanVariables.empty() )
        {
            const string* toDelete = mBooleanVariables.back();
            mBooleanVariables.pop_back();
            delete toDelete;
        }
        mAuxiliaryBoolVarCounter = 0;
        mConstraints.insert( mConsistentConstraint );
        mConstraints.insert( mInconsistentConstraint );
        mExternalNamesToVariables.clear();
        mIdAllocator = 3;
    }
    
    const Constraint* ConstraintPool::newBound( const carl::Variable& _var, const Constraint::Relation _rel, const Rational& _bound )
    {
        CONSTRAINT_LOCK_GUARD
        // TODO: Maybe it's better to increment the allocator even if the constraint already exists.
        //       Avoids long waiting for access (mutual exclusion) but increases the allocator to fast.
        Constraint* constraint = createNormalizedBound( _var, _rel, _bound );
        auto iterBoolPair = mConstraints.insert( constraint );
        if( !iterBoolPair.second )
            delete constraint;
        return *iterBoolPair.first;
    }

    const Constraint* ConstraintPool::newConstraint( const Polynomial& _lhs, const Constraint::Relation _rel )
    {
        CONSTRAINT_LOCK_GUARD
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

    carl::Variable ConstraintPool::newArithmeticVariable( const string& _name, carl::VariableType _domain, bool _parsed )
    {
        assert( !_name.empty() );
        assert( _domain == carl::VariableType::VT_REAL || _domain == carl::VariableType::VT_INT );
        // Initialize the prefix for the external representation of internally generated (not parsed) variable names
        if( _parsed ) mExternalPrefixInitialized = false;
        else if( !mExternalPrefixInitialized ) initExternalPrefix();
        lock_guard<mutex> lock( mMutexArithmeticVariables );
        // Create the arithmetic variable
        auto iterBoolPair = mExternalNamesToVariables.insert( pair<string,carl::Variable>( _name, mVariablePool.getFreshVariable( _domain ) ) );
        assert( iterBoolPair.second );
        mVariablePool.setVariableName( iterBoolPair.first->second, _name );
        return iterBoolPair.first->second;
    }
    
    const string* ConstraintPool::newBooleanVariable( const string& _name, bool _parsed )
    {
        lock_guard<mutex> lock( mMutexBooleanVariables );
        assert( !booleanExistsAlready( _name ) );
        if( _parsed ) mExternalPrefixInitialized = false;
        else if( !mExternalPrefixInitialized ) initExternalPrefix();
        string* result = new string( _name );
        mBooleanVariables.push_back( result );
        return result;
    }

    const string* ConstraintPool::newAuxiliaryBooleanVariable( const std::string& _externalPrefix )
    {
        stringstream out;
        mMutexBooleanVariables.lock();
        out << mExternalVarNamePrefix << _externalPrefix << mAuxiliaryBoolVarCounter++;
        mMutexBooleanVariables.unlock();
        return newBooleanVariable( out.str() );;
    }
    
    void ConstraintPool::initExternalPrefix()
    {
        bool foundExternalPrefix = false;
        while( !foundExternalPrefix )
        {
            auto varName = mParsedVarNames.begin(); 
            while( varName != mParsedVarNames.end() )
            {
                unsigned pos = 0;
                while( pos < varName->size() && pos < mExternalVarNamePrefix.size() && varName->at( pos ) == mExternalVarNamePrefix.at( pos ) ) ++pos;
                if( pos == mExternalVarNamePrefix.size() - 1 )
                {
                    mExternalVarNamePrefix += "_";
                    break;
                }
                ++varName;
            }
            if( varName == mParsedVarNames.end() ) foundExternalPrefix = true;
        }
    }

    Constraint* ConstraintPool::createNormalizedBound( const carl::Variable& _var, const Constraint::Relation _rel, const Rational& _bound ) const
    {
        assert( _rel != Constraint::EQ && _rel != Constraint::NEQ );
        if( _rel == Constraint::GREATER )
        {
            Polynomial lhs = Polynomial( _bound ) - Polynomial( _var );
            return new Constraint( lhs, Constraint::LESS, mIdAllocator );
        }
        else if( _rel == Constraint::GEQ )
        {
            Polynomial lhs = Polynomial( _bound ) - Polynomial( _var );
            return new Constraint( lhs, Constraint::LEQ, mIdAllocator );
        }
        else
        {
            Polynomial lhs = Polynomial( _var ) - Polynomial( _bound );
            return new Constraint( lhs, _rel, mIdAllocator );
        }
    }
    
    Constraint* ConstraintPool::createNormalizedConstraint( const Polynomial& _lhs, const Constraint::Relation _rel ) const
    {
        if( _rel == Constraint::GREATER )
        {
            Polynomial lhs = _lhs.isZero() ? ZERO_POLYNOMIAL : -_lhs.coprimeCoefficients();
            assert( _lhs.isZero() || (_lhs.lterm()->coeff() < 0) == (_lhs.coprimeCoefficients().lterm()->coeff() < 0) );
            return new Constraint( lhs, Constraint::LESS );
        }
        else if( _rel == Constraint::GEQ )
        {
            Polynomial lhs = _lhs.isZero() ? ZERO_POLYNOMIAL : -_lhs.coprimeCoefficients();
            assert( _lhs.isZero() || (_lhs.lterm()->coeff() < 0) == (_lhs.coprimeCoefficients().lterm()->coeff() < 0) );
            return new Constraint( lhs, Constraint::LEQ );
        }
        else
        {
            Polynomial lhs = _lhs.isZero() ? ZERO_POLYNOMIAL : _lhs.coprimeCoefficients();
            assert( _lhs.isZero() || (_lhs.lterm()->coeff() < 0) == (_lhs.coprimeCoefficients().lterm()->coeff() < 0) );
            if( _rel == Constraint::EQ || _rel == Constraint::NEQ ) 
            {
                if( !_lhs.isZero() && lhs.lterm()->coeff() < ZERO_RATIONAL ) lhs = -lhs;
            }
            return new Constraint( lhs, _rel );
        }
    }

    const Constraint* ConstraintPool::addConstraintToPool( Constraint* _constraint )
    {
        _constraint->init();
        unsigned constraintConsistent = _constraint->isConsistent();
//        cout << *_constraint << " is consistent: " << constraintConsistent << endl;
        if( constraintConsistent == 2 ) // Constraint contains variables.
        {
            auto iterBoolPair = mConstraints.insert( _constraint );
            if( !iterBoolPair.second ) // Constraint has already been generated.
                delete _constraint;
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
                        delete constraint;
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
            delete _constraint;
            return (constraintConsistent ? mConsistentConstraint : mInconsistentConstraint );
        }
    }

    void ConstraintPool::print( ostream& _out ) const
    {
        CONSTRAINT_LOCK_GUARD
        _out << "---------------------------------------------------" << endl;
        _out << "Constraint pool:" << endl;
        for( auto constraint = mConstraints.begin(); constraint != mConstraints.end(); ++constraint )
            _out << "    " << **constraint << "  [id=" << (*constraint)->id() << ", hash=" << (*constraint)->getHash() << "]" << endl;
        _out << "---------------------------------------------------" << endl;
    }

}    // namespace smtrat

