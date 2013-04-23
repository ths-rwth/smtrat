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
 * @version 2012-10-13
 */

#include "ConstraintPool.h"

using namespace std;
using namespace GiNaC;

namespace smtrat
{
    /**
     *
     * @param _capacity
     */
    ConstraintPool::ConstraintPool( unsigned _capacity ):
        mExternalPrefixInitialized( true ),
        mIdAllocator( 1 ),
        mAuxiliaryBoolVarCounter( 0 ),
        mAuxiliaryRealVarCounter( 0 ),
        mAuxiliaryIntVarCounter( 0 ),
        mArithmeticVarCounter( 0 ),
        mConsistentConstraint( new Constraint( 0, CR_EQ, symtab(), 1 ) ),
        mInconsistentConstraint( new Constraint( 0, CR_LESS, symtab(), 2 ) ),
        mInternalRealVarNamePrefix( "r_" ),
        mInternalIntVarNamePrefix( "i_" ),
        mExternalVarNamePrefix( "_" ),
        mInternalToExternalVarNames(),
        mArithmeticVariables(),
        mBooleanVariables(),
        mConstraints(),
        mDomain()
    {
        mConstraints.reserve( _capacity );
        mConstraints.insert( mConsistentConstraint );
        mConstraints.insert( mInconsistentConstraint );
        mIdAllocator = 3;
    }

    /**
     *
     */
    ConstraintPool::~ConstraintPool()
    {
        while( !mConstraints.empty() )
        {
            const Constraint* pCons = (*mConstraints.begin());
            mConstraints.erase( mConstraints.begin() );
            delete pCons;
        }
    }

    /**
     *
     */
    void ConstraintPool::clear()
    {
        lock_guard<mutex> lock1( mMutexAllocator );
        lock_guard<mutex> lock2( mMutexArithmeticVariables );
        lock_guard<mutex> lock3( mMutexBooleanVariables );
        lock_guard<mutex> lock4( mMutexDomain );
        CONSTRAINT_LOCK_GUARD
        mConstraints.erase( mConsistentConstraint );
        mConstraints.erase( mInconsistentConstraint );
        while( !mConstraints.empty() )
        {
            const Constraint* pCons = (*mConstraints.begin());
            mConstraints.erase( mConstraints.begin() );
            delete pCons;
        }
        mArithmeticVariables.clear();
        mAuxiliaryRealVarCounter = 0;
        mAuxiliaryIntVarCounter = 0;
        mBooleanVariables.clear();
        mAuxiliaryBoolVarCounter = 0;
        mArithmeticVarCounter = 0;
        mConstraints.insert( mConsistentConstraint );
        mConstraints.insert( mInconsistentConstraint );
        mInternalToExternalVarNames.clear();
        mIdAllocator = 3;
    }

    /**
     *
     * @return
     */
    unsigned ConstraintPool::maxLenghtOfVarName() const
    {
        unsigned result = 0;
        for( symtab::const_iterator var = mArithmeticVariables.begin(); var != mArithmeticVariables.end(); ++var )
        {
            if( var->first.size() > result ) result = var->first.size();
        }
        for( set<string>::const_iterator var = mBooleanVariables.begin(); var != mBooleanVariables.end(); ++var )
        {
            if( var->size() > result ) result = var->size();
        }
        return result;
    }

    /**
     *
     * @param _lhs
     * @param _rel
     * @param _variables
     * @return
     */
    const Constraint* ConstraintPool::newConstraint( const ex& _lhs, const Constraint_Relation _rel, const symtab& _variables )
    {
        CONSTRAINT_LOCK_GUARD
        assert( hasNoOtherVariables( _lhs ) );
        // TODO: Maybe it's better to increment the allocator even if the constraint already exists.
        //       Avoids long waiting for access (mutual exclusion) but increases the allocator to fast.
        const Constraint* result = addConstraintToPool( createNormalizedConstraint( _lhs, _rel, _variables ) );
        return result;
    }

    /**
     *
     * @param _lhs
     * @param _rhs
     * @param _rel
     * @param _variables
     * @return
     */
    const Constraint* ConstraintPool::newConstraint( const ex& _lhs, const ex& _rhs, const Constraint_Relation _rel, const symtab& _variables )
    {
        CONSTRAINT_LOCK_GUARD
        assert( hasNoOtherVariables( _lhs ) && hasNoOtherVariables( _rhs ) );
        // TODO: Maybe it's better to increment the allocator even if the constraint already exists.
        //       Avoids long waiting for access (mutual exclusion) but increases the allocator to fast.
        const Constraint* result = addConstraintToPool( createNormalizedConstraint( _lhs-_rhs, _rel, _variables ) );
        return result;
    }

    /**
     *
     * @param _name
     * @return
     */
    pair<string,ex> ConstraintPool::newArithmeticVariable( const string& _name, Variable_Domain _domain, bool _parsed )
    {
        // Initialize the prefix for the external representation of internally generated (not parsed) variable names
        if( _parsed ) mExternalPrefixInitialized = false;
        else if( !mExternalPrefixInitialized ) initExternalPrefix();
        lock_guard<mutex> lock( mMutexArithmeticVariables );
        // Fix the internal name (used in GiNaC) of this variable
        stringstream out;
        if( _domain == REAL_DOMAIN ) out << mInternalRealVarNamePrefix;
        else out << mInternalIntVarNamePrefix;
        out << mArithmeticVarCounter++;
        mInternalToExternalVarNames[out.str()] = _name;
        // Create the GiNaC variable
        symtab emptySymtab;
        parser reader( emptySymtab );
        ex var = reader( out.str() );
        // Set the variable's domain
        mMutexDomain.lock();
        mDomain.insert( pair< ex, Variable_Domain >( var, _domain ) );
        mMutexDomain.unlock();
        return *mArithmeticVariables.insert( pair<string, ex>( out.str(), var ) ).first;
    }

    /**
     *
     * @return
     */
    pair<string,ex> ConstraintPool::newAuxiliaryRealVariable( const std::string& _externalPrefix )
    {
        stringstream out;
        out << mExternalVarNamePrefix << _externalPrefix << "_" << mAuxiliaryRealVarCounter++;
        return newArithmeticVariable( out.str(), REAL_DOMAIN );
    }

    /**
     *
     * @return
     */
    pair<string,ex> ConstraintPool::newAuxiliaryIntVariable( const std::string& _externalPrefix )
    {
        stringstream out;
        out << mExternalVarNamePrefix << _externalPrefix << mAuxiliaryIntVarCounter++;
        return newArithmeticVariable( out.str(), INTEGER_DOMAIN );
    }

    /**
     *
     * @param _name
     */
    void ConstraintPool::newBooleanVariable( const string& _name, bool _parsed )
    {
        lock_guard<mutex> lock( mMutexBooleanVariables );
        assert( mBooleanVariables.find( _name ) == mBooleanVariables.end() );
        if( _parsed ) mExternalPrefixInitialized = false;
        else if( !mExternalPrefixInitialized ) initExternalPrefix();
        mBooleanVariables.insert( _name );
    }

    /**
     *
     * @return
     */
    string ConstraintPool::newAuxiliaryBooleanVariable( const std::string& _externalPrefix )
    {
        stringstream out;
        mMutexBooleanVariables.lock();
        out << mExternalVarNamePrefix << _externalPrefix << mAuxiliaryBoolVarCounter++;
        mMutexBooleanVariables.unlock();
        newBooleanVariable( out.str() );
        return out.str();
    }
    
    /**
     * 
     */
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

    /**
     * Determines the highest degree occurring in all constraints.
     *
     * Note: This method makes the other accesses to the constraint pool waiting.
     * @return The highest degree occurring in all constraints
     */
    int ConstraintPool::maxDegree() const
    {
        int result = 0;
        CONSTRAINT_LOCK_GUARD
        for( fcs_const_iterator constraint = mConstraints.begin();
             constraint != mConstraints.end(); ++constraint )
        {
            int maxdeg = (*constraint)->maxDegree();
            if(maxdeg > result) result = maxdeg;
        }
        return result;
    }

    /**
     *
     * Note: This method makes the other accesses to the constraint pool waiting.
     * @return
     */
    unsigned ConstraintPool::nrNonLinearConstraints() const
    {
        unsigned nonlinear = 0;
        CONSTRAINT_LOCK_GUARD
        for( fcs_const_iterator constraint = mConstraints.begin();
             constraint != mConstraints.end(); ++constraint )
        {
            if(!(*constraint)->isLinear()) ++nonlinear;
        }
        return nonlinear;
    }

    /**
     *
     * @param _expression
     * @return
     */
    bool ConstraintPool::hasNoOtherVariables( const ex& _expression ) const
    {
        lst substitutionList = lst();
        lock_guard<mutex> lock( mMutexArithmeticVariables );
        for( symtab::const_iterator var = mArithmeticVariables.begin(); var != mArithmeticVariables.end(); ++var )
        {
            substitutionList.append( ex_to<symbol>( var->second ) == 0 );
        }
        bool result = _expression.subs( substitutionList ).info( info_flags::rational );
        return result;
    }

    /**
     *
     * Note, that this method uses the allocator which is locked before calling.
     *
     * @param _lhs
     * @param _rel
     * @param _variables
     * @return
     */
    Constraint* ConstraintPool::createNormalizedConstraint( const ex& _lhs, const Constraint_Relation _rel, const symtab& _variables ) const
    {
        if( _rel == CR_GREATER )
        {
            return new Constraint( -_lhs, CR_LESS, _variables, mIdAllocator );
        }
        else if( _rel == CR_GEQ )
        {
            return new Constraint( -_lhs, CR_LEQ, _variables, mIdAllocator );
        }
        else
        {
            return new Constraint( _lhs, _rel, _variables, mIdAllocator );
        }
    }

    /**
     *
     * Note, that this method uses the allocator which is locked before calling.
     *
     * @param _constraint
     * @return
     */
    const Constraint* ConstraintPool::addConstraintToPool( Constraint* _constraint )
    {
        unsigned constraintConsistent = _constraint->isConsistent();
        if( constraintConsistent == 2 )
        {
            // Constraint contains variables.
            pair<fastConstraintSet::iterator, bool> iterBoolPair = mConstraints.insert( _constraint );
            if( !iterBoolPair.second )
            {
                // Constraint has already been generated.
                delete _constraint;
            }
            else
            {
                _constraint->collectProperties();
                Constraint* constraint = _constraint->simplify();
                if( constraint != NULL )
                {
                    // Constraint could be simplified.
                    pair<fastConstraintSet::iterator, bool> iterBoolPairB = mConstraints.insert( constraint );
                    if( !iterBoolPairB.second )
                    {
                        // Simplified version already exists, then set the id of the generated constraint to the id of the simplified one.
                        _constraint->rId() = (*iterBoolPairB.first)->id();
                        delete constraint;
                    }
                    else
                    {
                        // Simplified version has not been generated before.
                        constraint->init();
                        ++mIdAllocator;
                    }
                    return *iterBoolPairB.first;
                }
                else
                {
                    // Constraint could not be simplified.
                    _constraint->init();
                    ++mIdAllocator;
                }
            }
            return *iterBoolPair.first;
        }
        else
        {
            // Constraint contains no variables.
            delete _constraint;
            return (constraintConsistent != 0 ? mConsistentConstraint : mInconsistentConstraint );
        }
    }
    
    /**
     * 
     * @param _varname
     * @return 
     */
    string ConstraintPool::externalName( const string& _varname ) const
    {
        auto iter = mInternalToExternalVarNames.find( _varname );
        assert( iter != mInternalToExternalVarNames.end() );
        return iter->second;
    }
    
    /**
     * Transforms the given expression to a string and replaces on the fly the internal GiNaC 
     * variables by their external representation.
     * 
     * @param _toTransform The expression to transform to a string.
     * 
     * @return The resulting string.
     */
    string ConstraintPool::stringOf( const ex& _toTransform ) const
    {
        string result = "";
        if( is_exactly_a<add>( _toTransform ) )
        {
            for( GiNaC::const_iterator subterm = _toTransform.begin(); subterm != _toTransform.end(); ++subterm )
            {
                if( subterm != _toTransform.begin() )
                {
                    result += "+";
                }
                result += stringOf( *subterm );
            }
        }
        else if( is_exactly_a<mul>( _toTransform ) )
        {
            for( GiNaC::const_iterator subterm = _toTransform.begin(); subterm != _toTransform.end(); ++subterm )
            {
                if( subterm != _toTransform.begin() )
                {
                    result += "*";
                }
                result += stringOf( *subterm );
            }
        }
        else if( is_exactly_a<power>( _toTransform ) )
        {
            assert( _toTransform.nops() == 2 );
            ex exponent = *(++_toTransform.begin());
            stringstream out;
            out << exponent;
            ex subterm = *_toTransform.begin();
            result += stringOf( subterm ) + "^" + out.str();
        }
        else if( is_exactly_a<numeric>( _toTransform ) )
        {
            numeric num = ex_to<numeric>( _toTransform );
            if( num.is_negative() )
            {
                result += "(-";
            }
            stringstream out;
            out << abs( num );
            result += out.str();
            if( num.is_negative() )
            {
                result += ")";
            }
        }
        else if( is_exactly_a<symbol>( _toTransform ) )
        {
            stringstream out;
            out << _toTransform;
            auto iter = mInternalToExternalVarNames.find( out.str() );
            assert( iter != mInternalToExternalVarNames.end() );
            result += iter->second;
        }
        else
        {
            assert( false );
        }
        return result;
    }

    /**
     * Prints all constraints in the constraint pool on the given stream.
     *
     * @param _out The stream to print on.
     */
    void ConstraintPool::print( ostream& _out ) const
    {
        CONSTRAINT_LOCK_GUARD
        _out << "---------------------------------------------------" << endl;
        _out << "Constraint pool:" << endl;
        for( fcs_const_iterator constraint = mConstraints.begin();
                constraint != mConstraints.end(); ++constraint )
        {
            _out << "    " << **constraint << endl;
        }
        _out << "---------------------------------------------------" << endl;
    }

    /**
     * Prints all variables in the constraint pool on the given stream.
     *
     * @param _out The stream to print on.
     */
    void ConstraintPool::printVariables( ostream& _out ) const
    {
        CONSTRAINT_LOCK_GUARD
        _out << "---------------------------------------------------" << endl;
        _out << "Arithmetic variable pool:" << endl;
        for( auto arithVar = mArithmeticVariables.begin(); arithVar != mArithmeticVariables.end(); ++arithVar )
        {
            _out << "    " << arithVar->first << "   ( " << toString( domain( arithVar->second ) ) << " )" << endl;
        }
        _out << "Boolean variable pool:" << endl;
        for( auto boolVar = mBooleanVariables.begin(); boolVar != mBooleanVariables.end(); ++boolVar )
        {
            _out << "    " << *boolVar << endl;
        }
        _out << "---------------------------------------------------" << endl;
    }

}    // namespace smtrat

