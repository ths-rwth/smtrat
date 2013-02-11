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
        mConsistentConstraint( new Constraint( 0, CR_EQ, symtab(), 1 ) ),
        mInconsistentConstraint( new Constraint( 0, CR_LESS, symtab(), 2 ) ),
        mAuxiliaryBooleanNamePrefix( "h_b_" ),
        mAuxiliaryRealNamePrefix( "h_r_" ),
        mAllRealVariables(),
        mAllBooleanVariables(),
        mAllConstraints()
    {
        mAllConstraints.reserve( _capacity );
        mAllConstraints.insert( mConsistentConstraint );
        mAllConstraints.insert( mInconsistentConstraint );
        mIdAllocator = 3;
    }

    /**
     *
     */
    ConstraintPool::~ConstraintPool()
    {
        while( !mAllConstraints.empty() )
        {
            const Constraint* pCons = *mAllConstraints.begin();
            mAllConstraints.erase( mAllConstraints.begin() );
            delete pCons;
        }
    }

    void ConstraintPool::clear()
    {
        mAllConstraints.erase( mConsistentConstraint );
        mAllConstraints.erase( mInconsistentConstraint );
        while( !mAllConstraints.empty() )
        {
            const Constraint* pCons = *mAllConstraints.begin();
            mAllConstraints.erase( mAllConstraints.begin() );
            delete pCons;
        }
        mAllRealVariables.clear();
        mAllBooleanVariables.clear();
        mAllConstraints.insert( mConsistentConstraint );
        mAllConstraints.insert( mInconsistentConstraint );
        mIdAllocator = 3;
    }

    /**
     *
     * @return
     */
    unsigned ConstraintPool::maxLenghtOfVarName() const
    {
        unsigned result = 0;
        for( symtab::const_iterator var = mAllRealVariables.begin(); var != mAllRealVariables.end(); ++var )
        {
            if( var->first.size() > result ) result = var->first.size();
        }
        for( set<string>::const_iterator var = mAllBooleanVariables.begin(); var != mAllBooleanVariables.end(); ++var )
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
        return addConstraintToPool( createNormalizedConstraint( _lhs, _rel, _variables ) );
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
        return addConstraintToPool( createNormalizedConstraint( _lhs-_rhs, _rel, _variables ) );
    }

    /**
     *
     * @param _name
     * @return
     */
    ex ConstraintPool::newRealVariable( const string& _name )
    {
        assert( mAllRealVariables.find( _name ) == mAllRealVariables.end() );
        symtab emptySymtab;
        parser reader( emptySymtab );
        ex var = reader( _name );
        return mAllRealVariables.insert( pair<const string, ex>( _name, var ) ).first->second;
    }

    /**
     *
     * @return
     */
    pair<string,ex> ConstraintPool::newAuxiliaryRealVariable()
    {
        stringstream out;
        out << mAuxiliaryRealNamePrefix << mAuxiliaryRealCounter++;
        assert( mAllRealVariables.find( out.str() ) == mAllRealVariables.end() );
        symtab emptySymtab;
        parser reader( emptySymtab );
        ex var = reader( out.str() );
        return *mAllRealVariables.insert( pair<const string, ex>( out.str(), var ) ).first;
    }

    /**
     *
     * @param _name
     */
    void ConstraintPool::newBooleanVariable( const string& _name )
    {
        assert( mAllBooleanVariables.find( _name ) == mAllBooleanVariables.end() );
        mAllBooleanVariables.insert( _name );
    }

    /**
     *
     * @return
     */
    string ConstraintPool::newAuxiliaryBooleanVariable()
    {
        stringstream out;
        out << mAuxiliaryBooleanNamePrefix << mAuxiliaryBooleanCounter++;
        mAllBooleanVariables.insert( out.str() );
        return out.str();
    }

    /**
     *
     * @param _out
     */
    void ConstraintPool::print( ostream& _out ) const
    {
        _out << "---------------------------------------------------" << endl;
        _out << "Constraint pool:" << endl;
        for( fcs_const_iterator constraint = mAllConstraints.begin();
                constraint != mAllConstraints.end(); ++constraint )
        {
            _out << "    " << **constraint << endl;
        }
        _out << "---------------------------------------------------" << endl;
    }

    /**
     * Constructs a new constraint using its string representation.
     *
     * @param _stringrep    String representation of the constraint.
     * @param _infix        true, if the given representation is in infix notation and false, if it is in prefix notation
     * @param _polarity     The polarity of the constraint.
     *
     * @return A shared pointer to the constraint.
     */
    const Constraint* ConstraintPool::newConstraint( const string& _stringrep, bool _infix, bool _polarity )
    {
        /*
         * Read the given string representing the constraint.
         */
        string expression;
        if( _infix )
        {
            expression = _stringrep;
        }
        else
        {
            expression = prefixToInfix( _stringrep );
        }
        string::size_type   opPos;
        Constraint_Relation relation;
        unsigned            opSize = 0;
        opPos = expression.find( "=", 0 );
        if( opPos == string::npos )
        {
            opPos = expression.find( "<", 0 );
            if( opPos == string::npos )
            {
                opPos = expression.find( ">", 0 );

                assert( opPos != string::npos );

                if( _polarity )
                {
                    relation = CR_GREATER;
                }
                else
                {
                    relation = CR_LEQ;
                }
                opSize = 1;
            }
            else
            {
                if( _polarity )
                {
                    relation = CR_LESS;
                }
                else
                {
                    relation = CR_GEQ;
                }
                opSize = 1;
            }
        }
        else
        {
            string::size_type tempOpPos = opPos;
            opPos = expression.find( "<", 0 );
            if( opPos == string::npos )
            {
                opPos = expression.find( ">", 0 );
                if( opPos == string::npos )
                {
                    opPos = expression.find( "!", 0 );
                    if( opPos == string::npos )
                    {
                        opPos = tempOpPos;
                        if( _polarity )
                        {
                            relation = CR_EQ;
                        }
                        else
                        {
                            relation = CR_NEQ;
                        }
                        opSize = 1;
                    }
                    else
                    {
                        if( _polarity )
                        {
                            relation = CR_NEQ;
                        }
                        else
                        {
                            relation = CR_EQ;
                        }
                        opSize = 2;
                    }
                }
                else
                {
                    if( _polarity )
                    {
                        relation = CR_GEQ;
                    }
                    else
                    {
                        relation = CR_LESS;
                    }
                    opSize = 2;
                }
            }
            else
            {
                if( _polarity )
                {
                    relation = CR_LEQ;
                }
                else
                {
                    relation = CR_GREATER;
                }
                opSize = 2;
            }
        }

        /*
         * Parse the lefthand and righthand side and store their difference as
         * lefthand side of the constraint.
         */
        parser reader( mAllRealVariables );
        ex lhs, rhs;
        string lhsString = expression.substr( 0, opPos );
        string rhsString = expression.substr( opPos + opSize );
        try
        {
            lhs = reader( lhsString );
            rhs = reader( rhsString );
        }
        catch( parse_error& err )
        {
            cerr << err.what() << endl;
        }

        /*
         * Collect the new variables in the constraint:
         */
        mAllRealVariables.insert( reader.get_syms().begin(), reader.get_syms().end() );
        return addConstraintToPool( createNormalizedConstraint( lhs-rhs, relation, reader.get_syms() ) );
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
     *
     * @return
     */
    int ConstraintPool::maxDegree() const
    {
        int result = 0;
        for( fcs_const_iterator constraint = mAllConstraints.begin();
             constraint != mAllConstraints.end(); ++constraint )
        {
            int maxdeg = (*constraint)->maxDegree();
            if(maxdeg > result) result = maxdeg;
        }
        return result;
    }

    /**
     *
     * @return
     */
    unsigned ConstraintPool::nrNonLinearConstraints() const
    {
        unsigned nonlinear = 0;
        for( fcs_const_iterator constraint = mAllConstraints.begin();
             constraint != mAllConstraints.end(); ++constraint )
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
        for( symtab::const_iterator var = mAllRealVariables.begin(); var != mAllRealVariables.end(); ++var )
        {
            substitutionList.append( ex_to<symbol>( var->second ) == 0 );
        }
        return _expression.subs( substitutionList ).info( info_flags::rational );
    }

    /**
     *
     * @param _lhs
     * @param _rel
     * @param _variables
     * @return
     */
    Constraint* ConstraintPool::createNormalizedConstraint( const ex& _lhs, const Constraint_Relation _rel, const symtab& _variables )
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
     * @param _constraint
     * @return
     */
    const Constraint* ConstraintPool::addConstraintToPool( Constraint* _constraint )
    {
        unsigned constraintConsistent = _constraint->isConsistent();
        if( constraintConsistent == 2 )
        {
            // Constraint contains variables.
            pair<fastConstraintSet::iterator, bool> iterBoolPair = mAllConstraints.insert( _constraint );
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
                    pair<fastConstraintSet::iterator, bool> iterBoolPairB = mAllConstraints.insert( constraint );
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


}    // namespace smtrat

