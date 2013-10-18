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
 * @version 2013-06-20
 */

#include "ConstraintPool.h"

using namespace std;

namespace smtrat
{
    /**
     * Constructor of the constraint pool.
     * 
     * @param _capacity Expected necessary capacity of the pool.
     */
    ConstraintPool::ConstraintPool( unsigned _capacity ):
        mExternalPrefixInitialized( true ),
        mIdAllocator( 1 ),
        mAuxiliaryBoolVarCounter( 0 ),
        mAuxiliaryRealVarCounter( 0 ),
        mAuxiliaryIntVarCounter( 0 ),
        mArithmeticVarCounter( 0 ),
        mConsistentConstraint( new Constraint( Polynomial( Rational( 0 ) ), Constraint::EQ, 1 ) ),
        mInconsistentConstraint( new Constraint( Polynomial( Rational( 0 ) ), Constraint::LESS, 2 ) ),
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

    /**
     * Resets the constraint pool.
     * 
     * Note: Do not use it. It is only made for the Benchmax.
     */
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
        mArithmeticVarCounter = 0;
        mConstraints.insert( mConsistentConstraint );
        mConstraints.insert( mInconsistentConstraint );
        mExternalNamesToVariables.clear();
        mIdAllocator = 3;
    }
    
    /**
     * Constructs a new constraint and adds it to the pool, if it is not yet a member. If it is a
     * member, this will be returned instead of a new constraint.
     * 
     * Note, that the left-hand side of the constraint is simplified and normalized, hence it is
     * not necessarily equal to the given left-hand side. The same holds for the relation symbol.
     * However, it is assured that the returned constraint has the same solutions as
     * the expected one.
     * 
     * @param _lhs The left-hand side of the constraint.
     * @param _rel The relation symbol of the constraint.
     * @param _variables An over-approximation of the variables which occur on the left-hand side.
     * @return The constructed constraint.
     */
    const Constraint* ConstraintPool::newBound( const carl::Variable& _var, const Constraint::Relation _rel, const Rational& _bound )
    {
        CONSTRAINT_LOCK_GUARD
        // TODO: Maybe it's better to increment the allocator even if the constraint already exists.
        //       Avoids long waiting for access (mutual exclusion) but increases the allocator to fast.
        Constraint* constraint = createNormalizedBound( _var, _rel, _bound );
        pair<fastConstraintSet::iterator, bool> iterBoolPair = mConstraints.insert( constraint );
        if( !iterBoolPair.second )
            delete constraint;
        return *iterBoolPair.first;
    }

    /**
     * Constructs a new constraint and adds it to the pool, if it is not yet a member. If it is a
     * member, this will be returned instead of a new constraint.
     * 
     * Note, that the left-hand side of the constraint is simplified and normalized, hence it is
     * not necessarily equal to the given left-hand side. The same holds for the relation symbol.
     * However, it is assured that the returned constraint has the same solutions as
     * the expected one.
     * 
     * @param _lhs The left-hand side of the constraint.
     * @param _rel The relation symbol of the constraint.
     * @param _variables An over-approximation of the variables which occur on the left-hand side.
     * @return The constructed constraint.
     */
    const Constraint* ConstraintPool::newConstraint( const Polynomial& _lhs, const Constraint::Relation _rel )
    {
        CONSTRAINT_LOCK_GUARD
        // TODO: Maybe it's better to increment the allocator even if the constraint already exists.
        //       Avoids long waiting for access (mutual exclusion) but increases the allocator to fast.
        Constraint* constraint = createNormalizedConstraint( _lhs, _rel );
        if( constraint->variables().empty() )
        {
            bool constraintConsistent = Constraint::evaluate( constraint->constantPart(), constraint->relation() );
            delete constraint;
            return ( constraintConsistent ? mConsistentConstraint : mInconsistentConstraint );
        }
        constraint->collectProperties();
        const Constraint* result = addConstraintToPool( constraint );
        return result;
    }

    /**
     * Creates an arithmetic variable.
     * @param _name The external name of the variable to construct.
     * @param _domain The domain of the variable to construct.
     * @param _parsed A special flag indicating whether this variable is constructed during parsing.
     * @return A pair of the internal name of the variable and the variable as an expression.
     */
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

    /**
     * Creates an auxiliary real valued variable.
     * 
     * @param _externalPrefix The prefix of the external name of the auxiliary variable to construct.
     * 
     * @return A pair of the internal name of the variable and the a variable as an expression.
     */
    carl::Variable ConstraintPool::newAuxiliaryRealVariable( const std::string& _externalPrefix )
    {
        stringstream out;
        out << mExternalVarNamePrefix << _externalPrefix << "_" << mAuxiliaryRealVarCounter++;
        return newArithmeticVariable( out.str(), carl::VariableType::VT_REAL );
    }

    /**
     * Creates an auxiliary integer valued variable.
     * 
     * @param _externalPrefix The prefix of the external name of the auxiliary variable to construct.
     * 
     * @return A pair of the internal name of the variable and the a variable as an expression.
     */
    carl::Variable ConstraintPool::newAuxiliaryIntVariable( const std::string& _externalPrefix )
    {
        stringstream out;
        out << mExternalVarNamePrefix << _externalPrefix << mAuxiliaryIntVarCounter++;
        return newArithmeticVariable( out.str(), carl::VariableType::VT_INT );
    }

    /**
     * 
     * @param _element
     * @return 
     */
    bool ConstraintPool::hasBoolean( const string& _element ) const
    {
        for( auto iter = mBooleanVariables.begin(); iter != mBooleanVariables.end(); ++iter )
        {
            if( **iter == _element ) return true;
        }
        return false;
    }
    
    /**
     * Creates a new Boolean variable.
     * 
     * @param _name The external name of the variable to construct.
     * @param _parsed A special flag indicating whether this variable is constructed during parsing.
     */
    const string* ConstraintPool::newBooleanVariable( const string& _name, bool _parsed )
    {
        lock_guard<mutex> lock( mMutexBooleanVariables );
        assert( !hasBoolean( _name ) );
        if( _parsed ) mExternalPrefixInitialized = false;
        else if( !mExternalPrefixInitialized ) initExternalPrefix();
        string* result = new string( _name );
        mBooleanVariables.push_back( result );
        return result;
    }

    /**
     * Creates an auxiliary Boolean variable.
     * 
     * @param _externalPrefix The prefix of the external name of the auxiliary variable to construct.
     * 
     * @return The internal name of the variable.
     */
    const string* ConstraintPool::newAuxiliaryBooleanVariable( const std::string& _externalPrefix )
    {
        stringstream out;
        mMutexBooleanVariables.lock();
        out << mExternalVarNamePrefix << _externalPrefix << mAuxiliaryBoolVarCounter++;
        mMutexBooleanVariables.unlock();
        return newBooleanVariable( out.str() );;
    }
    
    /**
     * Initializes the prefix of the external variable names of internally declared (not parsed) variables.
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
            int maxdeg = (*constraint)->lhs().highestDegree();
            if(maxdeg > result) result = maxdeg;
        }
        return result;
    }

    /**
     * Determines the number of non-linear constraints in the pool.
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
            if(!(*constraint)->lhs().isLinear()) ++nonlinear;
        }
        return nonlinear;
    }

    /**
     * Creates a normalized constraint, which has the same solutions as the constraint consisting of the given
     * left-hand side and relation symbol.
     * 
     * Note, that this method uses the allocator which is locked before calling.
     *
     * @param _lhs The left-hand side of the constraint before normalization,
     * @param _rel The relation symbol of the constraint before normalization,
     * @param _variables An over-approximation of the variables occurring in the given left-hand side.
     * 
     * @return The constructed constraint.
     */
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
    
    /**
     * Creates a normalized constraint, which has the same solutions as the constraint consisting of the given
     * left-hand side and relation symbol.
     * 
     * Note, that this method uses the allocator which is locked before calling.
     *
     * @param _lhs The left-hand side of the constraint before normalization,
     * @param _rel The relation symbol of the constraint before normalization,
     * @param _variables An over-approximation of the variables occurring in the given left-hand side.
     * 
     * @return The constructed constraint.
     */
    Constraint* ConstraintPool::createNormalizedConstraint( const Polynomial& _lhs, const Constraint::Relation _rel ) const
    {
        if( _rel == Constraint::GREATER )
        {
            Polynomial lhs = -_lhs.coprimeCoefficients();
            assert( (_lhs.trailingTerm()->coeff() < 0) == (_lhs.coprimeCoefficients().trailingTerm()->coeff() < 0) );
            return new Constraint( lhs, Constraint::LESS, mIdAllocator );
        }
        else if( _rel == Constraint::GEQ )
        {
            Polynomial lhs = -_lhs.coprimeCoefficients();
            assert( (_lhs.trailingTerm()->coeff() < 0) == (_lhs.coprimeCoefficients().trailingTerm()->coeff() < 0) );
            return new Constraint( lhs, Constraint::LEQ, mIdAllocator );
        }
        else
        {
            assert( (_lhs.trailingTerm()->coeff() < 0) == (_lhs.coprimeCoefficients().trailingTerm()->coeff() < 0) );
            Polynomial lhs = _lhs.coprimeCoefficients();
            if( _rel == Constraint::EQ || _rel == Constraint::NEQ ) 
            {
                if( lhs.trailingTerm()->coeff() < 0 ) lhs = -lhs;
            }
            return new Constraint( lhs, _rel, mIdAllocator );
        }
    }

    /**
     * Adds the given constraint to the pool, if it does not yet occur in there.
     * 
     * Note, that this method uses the allocator which is locked before calling.
     * 
     * @sideeffect The given constraint will be deleted, if it already occurs in the pool.
     *
     * @param _constraint The constraint to add to the pool.
     * 
     * @return The given constraint, if it did not yet occur in the pool;
     *          The equivalent constraint already occurring in the pool.
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
            return (constraintConsistent ? mConsistentConstraint : mInconsistentConstraint );
        }
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

}    // namespace smtrat

