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
        mIdAllocator( 1 ),
        mAuxiliaryBooleanCounter( 0 ),
        mAuxiliaryRealCounter( 0 ),
        mConsistentConstraint( new std::atomic< const Constraint* >( new Constraint( 0, CR_EQ, symtab(), 1 ) ) ),
        mInconsistentConstraint( new std::atomic< const Constraint* >( new Constraint( 0, CR_LESS, symtab(), 2 ) ) ),
        mAuxiliaryBooleanNamePrefix( "h_b_" ),
        mAuxiliaryRealNamePrefix( "h_r_" ),
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
            const Constraint* pCons = (*mConstraints.begin())->load();
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
        lock_guard<mutex> lock5( mMutexConstraints );
        mConstraints.erase( mConsistentConstraint );
        mConstraints.erase( mInconsistentConstraint );
        while( !mConstraints.empty() )
        {
            const Constraint* pCons = (*mConstraints.begin())->load();
            mConstraints.erase( mConstraints.begin() );
            delete pCons;
        }
        mArithmeticVariables.clear();
        mBooleanVariables.clear();
        mConstraints.insert( mConsistentConstraint );
        mConstraints.insert( mInconsistentConstraint );
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
        assert( hasNoOtherVariables( _lhs ) );
        // TODO: Maybe it's better to increment the allocator even if the constraint already exists.
        //       Avoids long waiting for access (mutual exclusion) but increases the allocator to fast.
        lock_guard<mutex> lock( mMutexAllocator );
        return addConstraintToPool( createNormalizedConstraint( _lhs, _rel, _variables ) )->load();
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
        assert( hasNoOtherVariables( _lhs ) && hasNoOtherVariables( _rhs ) );
        // TODO: Maybe it's better to increment the allocator even if the constraint already exists.
        //       Avoids long waiting for access (mutual exclusion) but increases the allocator to fast.
        lock_guard<mutex> lock( mMutexAllocator );
        return addConstraintToPool( createNormalizedConstraint( _lhs-_rhs, _rel, _variables ) )->load();
    }

    /**
     *
     * @param _name
     * @return
     */
    ex ConstraintPool::newArithmeticVariable( const string& _name, Variable_Domain _domain )
    {
        assert( mArithmeticVariables.find( _name ) == mArithmeticVariables.end() );
        symtab emptySymtab;
        parser reader( emptySymtab );
        ex var = reader( _name );
        mMutexDomain.lock();
        auto res = mDomain.insert( pair< ex, Variable_Domain >( var, _domain ) );
        assert( res.second );
        mMutexDomain.unlock();
        lock_guard<mutex> lock( mMutexArithmeticVariables );
        return mArithmeticVariables.insert( pair<const string, ex>( _name, var ) ).first->second;
    }

    /**
     *
     * @return
     */
    pair<string,ex> ConstraintPool::newAuxiliaryRealVariable()
    {
        stringstream out;
        out << mAuxiliaryRealNamePrefix << mAuxiliaryRealCounter++;
        assert( mArithmeticVariables.find( out.str() ) == mArithmeticVariables.end() );
        symtab emptySymtab;
        parser reader( emptySymtab );
        ex var = reader( out.str() );
        mMutexDomain.lock();
        auto res = mDomain.insert( pair< ex, Variable_Domain >( var, REAL_DOMAIN ) );
        assert( res.second );
        mMutexDomain.unlock();
        lock_guard<mutex> lock( mMutexArithmeticVariables );
        return *mArithmeticVariables.insert( pair<const string, ex>( out.str(), var ) ).first;
    }

    /**
     *
     * @param _name
     */
    void ConstraintPool::newBooleanVariable( const string& _name )
    {
        lock_guard<mutex> lock( mMutexBooleanVariables );
        assert( mBooleanVariables.find( _name ) == mBooleanVariables.end() );
        mBooleanVariables.insert( _name );
    }

    /**
     *
     * @return
     */
    string ConstraintPool::newAuxiliaryBooleanVariable()
    {
        lock_guard<mutex> lock( mMutexBooleanVariables );
        stringstream out;
        out << mAuxiliaryBooleanNamePrefix << mAuxiliaryBooleanCounter++;
        mBooleanVariables.insert( out.str() );
        return out.str();
    }

    /**
     * Prints all constraints in the constraint pool on the given stream.
     *
     * @param _out The stream to print on.
     */
    void ConstraintPool::print( ostream& _out ) const
    {
        lock_guard<mutex> lock( mMutexConstraints );
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
     * Transforms the constraint in prefix notation to a constraint in infix notation.
     *
     * @param   _prefixRep  The prefix notation of the contraint to transform.
     *
     * @return The infix notation of the constraint.
     */
    string ConstraintPool::prefixToInfix( const string& _prefixRep )
    {
        assert( !_prefixRep.empty() );

        if( _prefixRep.at( 0 ) == '(' )
        {
            string op  = string( "" );
            string lhs = string( "" );
            string rhs = string( "" );
            unsigned pos               = 1;
            unsigned numOpeningBracket = 0;
            unsigned numClosingBracket = 0;
            while( pos < _prefixRep.length() && _prefixRep.at( pos ) != ' ' )
            {
                assert( _prefixRep.at( pos ) != '(' );
                assert( _prefixRep.at( pos ) != ')' );
                op += _prefixRep.at( pos );
                pos++;
            }

            assert( pos != _prefixRep.length() );
            pos++;

            while( pos < _prefixRep.length() )
            {
                if( _prefixRep.at( pos ) == '(' )
                {
                    numOpeningBracket++;
                    lhs += _prefixRep.at( pos );
                }
                else if( _prefixRep.at( pos ) == ')' && numOpeningBracket > numClosingBracket )
                {
                    numClosingBracket++;
                    lhs += _prefixRep.at( pos );
                }
                else if( (_prefixRep.at( pos ) == ' ' && numOpeningBracket == numClosingBracket)
                         || (_prefixRep.at( pos ) == ')' && numOpeningBracket == numClosingBracket) )
                {
                    break;
                }
                else
                {
                    lhs += _prefixRep.at( pos );
                }
                pos++;
            }

            assert( pos != _prefixRep.length() );

            if( _prefixRep.at( pos ) == ')' )
            {
                assert( op.compare( "-" ) == 0 );

                string result = "(-1)*(" + prefixToInfix( lhs ) + ")";
                return result;
            }
            string result = "(" + prefixToInfix( lhs ) + ")";
            while( _prefixRep.at( pos ) != ')' )
            {
                rhs = "";
                pos++;
                while( pos < _prefixRep.length() )
                {
                    if( _prefixRep.at( pos ) == '(' )
                    {
                        numOpeningBracket++;
                        rhs += _prefixRep.at( pos );
                    }
                    else if( _prefixRep.at( pos ) == ')' && numOpeningBracket > numClosingBracket )
                    {
                        numClosingBracket++;
                        rhs += _prefixRep.at( pos );
                    }
                    else if( (_prefixRep.at( pos ) == ' ' || _prefixRep.at( pos ) == ')') && numOpeningBracket == numClosingBracket )
                    {
                        break;
                    }
                    else
                    {
                        rhs += _prefixRep.at( pos );
                    }
                    pos++;
                }

                assert( pos != _prefixRep.length() );

                result += op + "(" + prefixToInfix( rhs ) + ")";
            }
            return result;
        }
        else
        {
            assert( _prefixRep.find( " ", 0 ) == string::npos );
            assert( _prefixRep.find( "(", 0 ) == string::npos );
            assert( _prefixRep.find( ")", 0 ) == string::npos );
            return _prefixRep;
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
        lock_guard<mutex> lock( mMutexConstraints );
        for( fcs_const_iterator constraint = mConstraints.begin();
             constraint != mConstraints.end(); ++constraint )
        {
            int maxdeg = (*constraint)->load()->maxDegree();
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
        lock_guard<mutex> lock( mMutexConstraints );
        for( fcs_const_iterator constraint = mConstraints.begin();
             constraint != mConstraints.end(); ++constraint )
        {
            if(!(*constraint)->load()->isLinear()) ++nonlinear;
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
        return _expression.subs( substitutionList ).info( info_flags::rational );
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
    std::atomic<const Constraint*>* ConstraintPool::addConstraintToPool( Constraint* _constraint )
    {
        unsigned constraintConsistent = _constraint->isConsistent();
        if( constraintConsistent == 2 )
        {
            std::unique_lock<std::mutex> lock( mMutexConstraints );
            // Constraint contains variables.
            pair<fastConstraintSet::iterator, bool> iterBoolPair = mConstraints.insert( new std::atomic<const Constraint*>( _constraint ) );
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
                    pair<fastConstraintSet::iterator, bool> iterBoolPairB = mConstraints.insert( new std::atomic<const Constraint*>( constraint ) );
                    if( !iterBoolPairB.second )
                    {
                        // Simplified version already exists, then set the id of the generated constraint to the id of the simplified one.
                        _constraint->rId() = (*iterBoolPairB.first)->load()->id();
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


}    // namespace smtrat

