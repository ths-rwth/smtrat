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
 * Constraint.cpp
 * @author Florian Corzilius
 * @author Sebastian Junges
 * @author Ulrich Loup
 * @since 2010-04-26
 * @version 2013-03-27
 */

#include <src/carl/core/VariablesInformation.h>

#include "Constraint.h"
#include "ConstraintPool.h"
#include "Formula.h"

using namespace std;
using namespace carl;

namespace smtrat
{
    const unsigned MAX_DEGREE_FOR_FACTORIZATION = 40;
    const unsigned MIN_DEGREE_FOR_FACTORIZATION = 2;
    const unsigned MAX_DIMENSION_FOR_FACTORIZATION = 6;
    const unsigned MAX_NUMBER_OF_MONOMIALS_FOR_FACTORIZATION = 300;

    recursive_mutex Constraint::mMutex;

    Constraint::Constraint():
        mID( 0 ),
        mSecondHash( EQ ),
        mHash( mFirstHash * 6 + mSecondHash ),
        mIsNeverPositive( false ),
        mIsNeverNegative( false ),
        mIsNeverZero( false ),
        mRelation( EQ ),
        mLhs( Rational( 0 ) ),
        mFactorization( 1, mLhs ),
        mVariables(),
        mVarInfoMap()
    {
        mFirstHash = mLhs.hash();
        mFactorization.push_back( mLhs );
    }

    Constraint::Constraint( const Polynomial& _lhs, const Relation _cr, unsigned _id ):
        mID( _id ),
        mFirstHash( _lhs.hash() ),
        mSecondHash( _cr ),
        mHash( mFirstHash * 6 + mSecondHash ),
        mIsNeverPositive( false ),
        mIsNeverNegative( false ),
        mIsNeverZero( false ),
        mRelation( _cr ),
        mLhs( _lhs ),
        mFactorization( 1, mLhs ),
        mVariables(),
        mVarInfoMap()
    {
        mLhs.gatherVariables( mVariables );
    }

    Constraint::Constraint( const Constraint& _constraint, bool _rehash ):
        mID( _constraint.id() ),
        mFirstHash( _rehash ? _constraint.mLhs.hash() : _constraint.firstHash() ),
        mSecondHash( _rehash ? _constraint.relation() : _constraint.secondHash() ),
        mHash( _rehash ? (mFirstHash * 6 + mSecondHash) : _constraint.hash() ),
        mIsNeverPositive( _constraint.mIsNeverPositive ),
        mIsNeverNegative( _constraint.mIsNeverNegative ),
        mIsNeverZero( _constraint.mIsNeverZero ),
        mRelation( _constraint.relation() ),
        mLhs( _constraint.mLhs ),
        mFactorization( _constraint.mFactorization ),
        mVariables( _constraint.variables() ),
        mVarInfoMap( _constraint.mVarInfoMap )
    {}

    Constraint::~Constraint()
    {}

    

    /**
     * Checks whether the given value satisfies the given relation to zero.
     * @param _value The value to compare with zero.
     * @param _relation The relation between the given value and zero.
     * @return true,  if the given value satisfies the given relation to zero;
     *          false, otherwise.
     */
    bool Constraint::evaluate( const Rational& _value, Relation _relation )
    {
        switch( _relation )
        {
            case EQ:
            {
                if( _value == 0 ) return true;
                else return false;
            }
            case NEQ:
            {
                if( _value == 0 ) return false;
                else return true;
            }
            case LESS:
            {
                if( _value < 0 ) return true;
                else return false;
            }
            case GREATER:
            {
                if( _value > 0 ) return true;
                else return false;
            }
            case LEQ:
            {
                if( _value <= 0 ) return true;
                else return false;
            }
            case GEQ:
            {
                if( _value >= 0 ) return true;
                else return false;
            }
            default:
            {
                cout << "Error in isConsistent: unexpected relation symbol." << endl;
                return false;
            }
        }
    }

    /**
     * Checks, whether the constraint is consistent.
     * It differs between, containing variables, consistent, and inconsistent.
     *
     * @return 0, if the constraint is not consistent.
     *          1, if the constraint is consistent.
     *          2, if the constraint still contains variables.
     */
    unsigned Constraint::isConsistent() const
    {
        if( variables().empty() )
        {
            return evaluate( constantPart(), relation() ) ? 1 : 0;
        }
        else
        {
            switch( relation() )
            {
                case EQ:
                {
                    if( mIsNeverZero ) return 0;
                    break;
                }
                case NEQ:
                {
                    if( mIsNeverZero ) return 1;
                    break;
                }
                case LESS:
                {
                    if( mIsNeverZero && mIsNeverPositive ) return 1;
                    if( mIsNeverNegative ) return 0;
                    break;
                }
                case GREATER:
                {
                    if( mIsNeverZero && mIsNeverNegative ) return 1;
                    if( mIsNeverPositive ) return 0;
                    break;
                }
                case LEQ:
                {
                    if( mIsNeverPositive ) return 1;
                    if( mIsNeverZero && mIsNeverNegative ) return 0;
                    break;
                }
                case GEQ:
                {
                    if( mIsNeverNegative ) return 1;
                    if( mIsNeverZero && mIsNeverPositive ) return 0;
                    break;
                }
                default:
                {
                    cout << "Error in isConsistent: unexpected relation symbol." << endl;
                    return false;
                }
            }
            return 2;
        }
    }
    
    /**
     * 
     * @param _solutionInterval
     * @return 
     */
    unsigned Constraint::consistentWith( const EvalDoubleIntervalMap& _solutionInterval ) const
    {
        if( variables().empty() )
        {
            return evaluate( constantPart(), relation() ) ? 1 : 0;
        }
        else
        {
            DoubleInterval solutionSpace = carl::IntervalEvaluation::evaluate( mLhs, _solutionInterval );
            if( solutionSpace.empty() )
            {
                return 2;
            }
            switch( relation() )
            {
                case EQ:
                {
                    if( solutionSpace.diameter() == 0 && solutionSpace.left() == 0 )
                    {
                        return 1;
                    }
                    else if( !solutionSpace.contains( 0 ) )
                    {
                        return 0;
                    }
                    break;
                }
                case NEQ:
                {
                    if( !solutionSpace.contains( 0 ) )
                    {
                        return 1;
                    }
                    break;
                }
                case LESS:
                {
                    if( solutionSpace.rightType() != DoubleInterval::INFINITY_BOUND )
                    {
                        if( solutionSpace.right() < 0 )
                        {
                            return 1;
                        }
                        else if( solutionSpace.right() == 0 && solutionSpace.rightType() == DoubleInterval::STRICT_BOUND ) return 1;
                    }
                    if( solutionSpace.leftType() != DoubleInterval::INFINITY_BOUND )
                    {
                        if( solutionSpace.left() >= 0 )
                        {
                            return 0;
                        }
                    }
                    break;
                }
                case GREATER:
                {
                    if( solutionSpace.leftType() != DoubleInterval::INFINITY_BOUND )
                    {
                        if( solutionSpace.left() > 0 )
                        {
                            return 1;
                        }
                        else if( solutionSpace.left() == 0 && solutionSpace.leftType() == DoubleInterval::STRICT_BOUND )
                        {
                            return 1;
                        }
                    }
                    if( solutionSpace.rightType() != DoubleInterval::INFINITY_BOUND )
                    {
                        if( solutionSpace.right() <= 0 )
                        {
                            return 0;
                        }
                    }
                    break;
                }
                case LEQ:
                {
                    if( solutionSpace.rightType() != DoubleInterval::INFINITY_BOUND )
                    {
                        if( solutionSpace.right() <= 0 )
                        {
                            return 1;
                        }
                    }
                    if( solutionSpace.leftType() != DoubleInterval::INFINITY_BOUND )
                    {
                        if( solutionSpace.left() > 0 )
                        {
                            return 0;
                        }
                        else if( solutionSpace.left() == 0 && solutionSpace.leftType() == DoubleInterval::STRICT_BOUND )
                        {
                            return 0;
                        }
                    }
                    break;
                }
                case GEQ:
                {
                    if( solutionSpace.leftType() != DoubleInterval::INFINITY_BOUND )
                    {
                        if( solutionSpace.left() >= 0 )
                        {
                            return 1;
                        }
                    }
                    if( solutionSpace.rightType() != DoubleInterval::INFINITY_BOUND )
                    {
                        if( solutionSpace.right() < 0 )
                        {
                            return 0;
                        }
                        else if( solutionSpace.right() == 0 && solutionSpace.rightType() == DoubleInterval::STRICT_BOUND )
                        {
                            return 0;
                        }
                    }
                    break;
                }
                default:
                {
                    cout << "Error in isConsistent: unexpected relation symbol." << endl;
                    return 0;
                }
            }
            return 2;
        }
    }

    /**
     * Checks whether the given assignment satisfies this constraint.
     *
     * @param _assignment The assignment.
     * @return 1, if the given assignment satisfies this constraint.
     *         0, if the given assignment contradicts this constraint.
     *         2, otherwise (possibly not defined for all variables in the constraint,
     *                       even then it could be possible to obtain the first two results.)
     */
    unsigned Constraint::satisfiedBy( std::map<carl::Variable,Rational>& _assignment ) const
    {
        Polynomial tmp = mLhs.substitute( _assignment );
        if( tmp.isConstant() )
        {
            return evaluate( tmp.trailingTerm()->coeff(), relation() ) ? 1 : 0;
        }
        else return 2;
    }

    /**
     * Calculates the coefficient of the given variable with the given degree. Note, that it only
     * computes the coefficient once and stores the result.
     *
     * @param _variable The variable for which to calculate the coefficient.
     * @param _degree The according degree of the variable for which to calculate the coefficient.
     * @return The ith coefficient of the given variable, where i is the given degree.
     */
    Polynomial Constraint::coefficient( const carl::Variable& _var, unsigned _degree ) const
    {
        Polynomial result;
//        mVarInfoMap.getVarInfo( _var )->updateCoeff( _degree, result );
        mLhs.
    }

    /**
     *
     * @param The relation
     * @return
     */
    bool constraintRelationIsStrict( Constraint::Relation rel )
    {
        return (rel == Constraint::NEQ || rel == Constraint::LESS || rel == Constraint::GREATER);
    }
    
    /**
     * Collects some properties of the constraint. Needs only to be applied once.
     */
    void Constraint::collectProperties()
    {
        mIsNeverPositive = true;
        mIsNeverNegative = true;
        mIsNeverZero = false;
        // TODO: run through the polynomial and check whether it (or the polynomial multplied by -1) is a sum of squares.
//        if( ( mConstantPart.is_negative() && mIsNeverPositive ) || ( mConstantPart.is_positive() && mIsNeverNegative ) )
//        {
//            mIsNeverZero = true;
//        }
    }
    
    /**
     * Applies some cheap simplifications to the constraints.
     *
     * @return The simplified constraints, if simplifications could be applied;
     *         The constraint itself, otherwise.
     */
    Constraint* Constraint::simplify()
    {
        bool anythingChanged = false;
        if( (mIsNeverNegative && mRelation == LEQ) || (mIsNeverPositive && mRelation == GEQ) )
        {
            anythingChanged = true;
            mRelation = EQ;
        }
        // Left-hand side is a non-linear monomial
        if( !mLhs.isLinear() && mLhs.nrTerms() == 1 )
        {
            switch( mRelation )
            {
                case EQ:
                {
                    mIsNeverPositive = false;
                    mIsNeverNegative = false;
                    mLhs = Polynomial( *mVariables.begin() );
                    anythingChanged = true;
                    break;
                }
                case NEQ:
                {
                    mIsNeverPositive = false;
                    mIsNeverNegative = false;
                    mLhs = Polynomial( *mVariables.begin() );
                    anythingChanged = true;
                    break;
                }
                case LEQ:
                {
                    if( mIsNeverPositive )
                    {
                        mLhs = Polynomial( Rational( -1 ) ) * Polynomial( *mVariables.begin() ) * Polynomial( *mVariables.begin() );
                        anythingChanged = true;
                    }
                    else
                    {
                        mLhs = (mLhs.trailingTerm()->coeff() > 0 ? Polynomial( Rational( 1 ) ) : Polynomial( Rational( -1 ) ) ) * Polynomial( *mVariables.begin() );
                        anythingChanged = true;
                    }
                    break;
                }
                case GEQ:
                {
                    if( mIsNeverNegative )
                    {
                        mLhs = Polynomial( *mVariables.begin() ) * Polynomial( *mVariables.begin() );
                        anythingChanged = true;
                    }
                    else
                    {
                        mLhs = (mLhs.trailingTerm()->coeff() > 0 ? Polynomial( Rational( 1 ) ) : Polynomial( Rational( -1 ) ) ) * Polynomial( *mVariables.begin() );
                        anythingChanged = true;
                    }
                    break;
                }
                case LESS:
                {
                    if( mIsNeverPositive )
                    {
                        mRelation = NEQ;
                        mLhs = Polynomial( *mVariables.begin() );
                        mIsNeverPositive = false;
                        anythingChanged = true;
                    }
                    else
                    {
                        if( mIsNeverNegative )
                        {
                            mLhs = Polynomial( *mVariables.begin() ) * Polynomial( *mVariables.begin() );
                            anythingChanged = true;
                        }
                        else
                        {
                            mLhs = (mLhs.trailingTerm()->coeff() > 0 ? Polynomial( Rational( 1 ) ) : Polynomial( Rational( -1 ) ) ) * Polynomial( *mVariables.begin() );
                            anythingChanged = true;
                        }
                    }
                    break;
                }
                case GREATER:
                {
                    if( mIsNeverNegative )
                    {
                        mRelation = NEQ;
                        mLhs = Polynomial( *mVariables.begin() );
                        mIsNeverNegative = false;
                        anythingChanged = true;
                    }
                    else
                    {
                        if( mIsNeverPositive )
                        {
                            mLhs = Polynomial( Rational( -1 ) ) * Polynomial( *mVariables.begin() ) * Polynomial( *mVariables.begin() );
                            anythingChanged = true;
                        }
                        else
                        {
                            mLhs = (mLhs.trailingTerm()->coeff() > 0 ? Polynomial( Rational( 1 ) ) : Polynomial( Rational( -1 ) ) ) * Polynomial( *mVariables.begin() );
                            anythingChanged = true;
                        }
                    }
                    break;
                }
                default:
                {
                    assert( false );
                }
            }
        }
        if( anythingChanged )
        {
            Constraint* constraint = new Constraint( *this, true );
            return constraint;
        }
        else
        {
            return NULL;
        }
    }

    /**
     * Initializes the stored factorization and the left-hand side with no multiple roots, if it is univariate.
     */
    void Constraint::init()
    {
        mLhs.getVarInfo( mVarInfoMap );
        #ifdef SMTRAT_STRAT_Factorization
        if( mNumMonomials <= MAX_NUMBER_OF_MONOMIALS_FOR_FACTORIZATION && mVariables.size() <= MAX_DIMENSION_FOR_FACTORIZATION
            && mMaxMonomeDegree <= MAX_DEGREE_FOR_FACTORIZATION && mMaxMonomeDegree >= MIN_DEGREE_FOR_FACTORIZATION )
        {
            mFactorization = factor( mLhs );
        }
        #endif
    }

    /**
     * Compares this constraint with the given constraint.
     *
     * @return  true,   if this constraint is LEXOGRAPHICALLY smaller than the given one;
     *          false,  otherwise.
     */
    bool Constraint::operator <( const Constraint& _constraint ) const
    {
        assert( mID > 0 && _constraint.id() > 0 );
        return mID < _constraint.id();
    }

    /**
     * Compares this constraint with the given constraint.
     *
     * @return  true,   if this constraint is equal to the given one;
     *          false,  otherwise.
     */
    bool Constraint::operator ==( const Constraint& _constraint ) const
    {
        assert( mID > 0 && _constraint.id() > 0 );
        return mID == _constraint.id();
    }

    /**
     * Prints the representation of the given constraints on the given stream.
     *
     * @param _ostream The stream to print on.
     * @param _constraint The constraint to print.
     * @return The given stream after printing.
     */
    ostream& operator <<( ostream& _ostream, const Constraint& _constraint )
    {
        _ostream << _constraint.toString();
        return _ostream;
    }

    /**
     * Gives the string representation of the constraint.
     *
     * @return The string representation of the constraint.
     */
    string Constraint::toString( unsigned _unequalSwitch, bool _infix, bool _friendlyVarNames ) const
    {
        string result = "";
        if( _infix )
            result = mLhs.toString( true, _friendlyVarNames );
        else
            result += "(";
        switch( relation() )
        {
            case EQ:
                result += "=";
                break;
            case NEQ:
                if( _infix )
                {
                    if( _unequalSwitch == 1 )
                        result += "<>";
                    else if( _unequalSwitch == 2 )
                        result += "/=";
                    else // standard case
                        result += "!=";
                }
                else
                {
                    if( _unequalSwitch == 0 ) // standard case
                        result += "!=";
                    else
                    {
                        string lhsString = mLhs.toString( true, _friendlyVarNames );
                        return "(or (< " + lhsString + " 0) (> " + lhsString + " 0))";
                    }
                }
                break;
            case LESS:
                result += "<";
                break;
            case GREATER:
                result += ">";
                break;
            case LEQ:
                result += "<=";
                break;
            case GEQ:
                result += ">=";
                break;
            default:
                result += "~";
        }
        result += (infix ? "0" : (mLhs.toString( true, _friendlyVarNames ) + " 0)"));
        return result;
    }


    
    /**
     * Prints the properties of this constraints on the given stream.
     *
     * @param _out The stream to print on.
     */
    void Constraint::printProperties( ostream& _out, bool _friendlyVarNames ) const
    {
        _out << "Properties:" << endl;
        _out << "   Is never positive?       " << (mIsNeverPositive ? "true" : "false") << endl;
        _out << "   Is never negative?       " << (mIsNeverNegative ? "true" : "false") << endl;
        _out << "   Cannot be zero?          " << (mIsNeverZero ? "true" : "false") << endl;
        _out << "   The number of monomials: " << mLhs.nrTerms() << endl;
        _out << "   The maximal degree:      " << mLhs.highestDegree() << endl;
        _out << "   The constant part:       " << constantPart() << endl;
        _out << "   Variables:" << endl;
        for( auto var = mVariables.begin(); var != mVarInfoMap.end(); ++var )
        {
            auto varInfo = mVarInfoMap.getVarInfo( *var );
            _out << "        " << varToString( *var, _friendlyVarNames ) << " has " << varInfo->occurence() << " occurences." << endl;
            _out << "        " << varToString( *var, _friendlyVarNames ) << " has the maximal degree of " << varInfo->maxDegree() << "." << endl;
            _out << "        " << varToString( *var, _friendlyVarNames ) << " has the minimal degree of " << varInfo->minDegree() << "." << endl;
        }
    }

    /**
     * Compares this constraint with the given constraint.
     *
     * @return  2,  if it is easy to decide that this constraint and the given constraint have the same solutions.(are equal)
     *          1,  if it is easy to decide that the given constraint includes all solutions of this constraint;
     *          -1, if it is easy to decide that this constraint includes all solutions of the given constraint;
     *          -2, if it is easy to decide that this constraint has no solution common with the given constraint;
     *          -3, if it is easy to decide that this constraint and the given constraint can be intersected;
     *          -4, if it is easy to decide that this constraint is the inverse of the given constraint;
     *          0,  otherwise.
     */
    signed Constraint::compare( const Constraint* _constraintA, const Constraint* _constraintB )
    {
        if( _constraintA->variables().empty() || _constraintB->variables().empty() ) return 0;
        auto var1 = _constraintA->variables().begin();
        auto var2 = _constraintB->variables().begin();
        while( var1 != _constraintA->variables().end() && var2 != _constraintB->variables().end() )
        {
            if( *var1 == *var2 )
            {
                var1++;
                var2++;
            }
            else
            {
                break;
            }
        }
        if( var1 == _constraintA->variables().end() && var2 == _constraintB->variables().end() )
        {
            ex leadingVar = ex( _constraintA->variables().begin()->second );
            ex lcoeffA = ex( _constraintA->coefficient( leadingVar, _constraintA->maxDegree( leadingVar ) ) );
            ex lcoeffB = ex( _constraintB->coefficient( leadingVar, _constraintB->maxDegree( leadingVar ) ) );
            ex lhsA    = ex( _constraintA->mLhs );
            ex lhsB    = ex( _constraintB->mLhs );
            if( lcoeffA.info( info_flags::rational ) && lcoeffB.info( info_flags::rational ) )
            {
                if( lcoeffB.info( info_flags::positive ) )
                {
                    lhsA = lhsA * lcoeffB;
                }
                else
                {
                    lhsA = lhsA * (-1) * lcoeffB;
                }
                if( lcoeffA.info( info_flags::positive ) )
                {
                    lhsB = lhsB * lcoeffA;
                }
                else
                {
                    lhsB = lhsB * (-1) * lcoeffA;
                }
            }
            else if( lcoeffA.info( info_flags::rational ) || lcoeffB.info( info_flags::rational ) )
            {
                return 0;
            }
            switch( _constraintB->relation() )
            {
                case EQ:
                {
                    switch( _constraintA->relation() )
                    {
                        case EQ:
                        {
                            ex result1 = lhsA - lhsB;
                            normalize( result1 );
                            if( result1 == 0 )
                                return 2;
                            if( result1.info( info_flags::rational ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2 == 0 )
                                return 2;
                            if( result2.info( info_flags::rational ) )
                                return -2;
                            return 0;
                        }
                        case NEQ:
                        {
                            ex result1 = lhsA - lhsB;
                            normalize( result1 );
                            if( result1 == 0 )
                                return -4;
                            if( result1.info( info_flags::rational ) )
                                return -1;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2 == 0 )
                                return -4;
                            if( result2.info( info_flags::rational ) )
                                return -1;
                            return 0;
                        }
                        case LESS:
                        {
                            ex result1 = lhsA - lhsB;
                            normalize( result1 );
                            if( result1.info( info_flags::negative ) )
                                return -1;
                            if( result1.info( info_flags::nonnegative ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2.info( info_flags::negative ) )
                                return -1;
                            if( result2.info( info_flags::nonnegative ) )
                                return -2;
                            return 0;
                        }
                        case GREATER:
                        {
                            ex result1 = -1 * (lhsA - lhsB);
                            normalize( result1 );
                            if( result1.info( info_flags::negative ) )
                                return -1;
                            if( result1.info( info_flags::nonnegative ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2 == 0 )
                                return -2;
                            if( result2.info( info_flags::negative ) )
                                return -2;
                            if( result2.info( info_flags::positive ) )
                                return -1;
                            return 0;
                        }
                        case LEQ:
                        {
                            ex result1 = -1 * (lhsA - lhsB);
                            normalize( result1 );
                            if( result1.info( info_flags::nonnegative ) )
                                return -1;
                            if( result1.info( info_flags::negative ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2 == 0 )
                                return -1;
                            if( result2.info( info_flags::negative ) )
                                return -1;
                            if( result2.info( info_flags::positive ) )
                                return -2;
                            return 0;
                        }
                        case GEQ:
                        {
                            ex result1 = lhsA - lhsB;
                            normalize( result1 );
                            if( result1.info( info_flags::nonnegative ) )
                                return -1;
                            if( result1.info( info_flags::negative ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2.info( info_flags::negative ) )
                                return -2;
                            if( result2.info( info_flags::nonnegative ) )
                                return -1;
                            return 0;
                        }
                        default:
                            return false;
                    }
                }
                case NEQ:
                {
                    switch( _constraintA->relation() )
                    {
                        case EQ:
                        {
                            ex result1 = lhsA - lhsB;
                            normalize( result1 );
                            if( result1 == 0 )
                                return -4;
                            if( result1.info( info_flags::rational ) )
                                return 1;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2 == 0 )
                                return -4;
                            if( result2.info( info_flags::rational ) )
                                return 1;
                            return 0;
                        }
                        case NEQ:
                        {
                            ex result1 = lhsA - lhsB;
                            normalize( result1 );
                            if( result1 == 0 )
                                return 2;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2 == 0 )
                                return 2;
                            return 0;
                        }
                        case LESS:
                        {
                            ex result1 = lhsA - lhsB;
                            normalize( result1 );
                            if( result1.info( info_flags::nonnegative ) )
                                return 1;
                            ex result2 = -1 * (lhsA + lhsB);
                            normalize( result2 );
                            if( result2.info( info_flags::nonnegative ) )
                                return 1;
                            return 0;
                        }
                        case GREATER:
                        {
                            ex result1 = -1 * (lhsA - lhsB);
                            normalize( result1 );
                            if( result1.info( info_flags::nonnegative ) )
                                return 1;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2.info( info_flags::nonnegative ) )
                                return 1;
                            return 0;
                        }
                        case LEQ:
                        {
                            ex result1 = lhsA - lhsB;
                            normalize( result1 );
                            if( result1 == 0 )
                                return -3;
                            if( result1.info( info_flags::positive ) )
                                return 1;
                            ex result2 = -1 * (lhsA + lhsB);
                            normalize( result2 );
                            if( result2 == 0 )
                                return -3;
                            if( result2.info( info_flags::positive ) )
                                return 1;
                            return 0;
                        }
                        case GEQ:
                        {
                            ex result1 = -1 * (lhsA - lhsB);
                            normalize( result1 );
                            if( result1 == 0 )
                                return -3;
                            if( result1.info( info_flags::positive ) )
                                return 1;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2 == 0 )
                                return -3;
                            if( result2.info( info_flags::positive ) )
                                return 1;
                            return 0;
                        }
                        default:
                            return 0;
                    }
                }
                case LESS:
                {
                    switch( _constraintA->relation() )
                    {
                        case EQ:
                        {
                            ex result1 = -1 * (lhsA - lhsB);
                            normalize( result1 );
                            if( result1.info( info_flags::negative ) )
                                return 1;
                            if( result1.info( info_flags::nonnegative ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2.info( info_flags::negative ) )
                                return 1;
                            if( result2.info( info_flags::nonnegative ) )
                                return -2;
                            return 0;
                        }
                        case NEQ:
                        {
                            ex result1 = -1 * (lhsA - lhsB);
                            normalize( result1 );
                            if( result1.info( info_flags::nonnegative ) )
                                return -1;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2.info( info_flags::nonnegative ) )
                                return -1;
                            return 0;
                        }
                        case LESS:
                        {
                            ex result1 = lhsA - lhsB;
                            normalize( result1 );
                            if( result1 == 0 )
                                return 2;
                            if( result1.info( info_flags::negative ) )
                                return -1;
                            if( result1.info( info_flags::positive ) )
                                return 1;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2.info( info_flags::nonnegative ) )
                                return -2;
                            return 0;
                        }
                        case GREATER:
                        {
                            ex result1 = -1 * (lhsA - lhsB);
                            normalize( result1 );
                            if( result1.info( info_flags::nonnegative ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2 == 0 )
                                return 2;
                            if( result2.info( info_flags::positive ) )
                                return -1;
                            if( result2.info( info_flags::negative ) )
                                return 1;
                            return 0;
                        }
                        case LEQ:
                        {
                            ex result1 = lhsA - lhsB;
                            normalize( result1 );
                            if( result1.info( info_flags::positive ) )
                                return 1;
                            if( result1.info( info_flags::rational ) )
                                return -1;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2.info( info_flags::positive ) )
                                return -2;
                            if( result2 == 0 )
                                return -4;
                            return 0;
                        }
                        case GEQ:
                        {
                            ex result1 = -1 * (lhsA - lhsB);
                            normalize( result1 );
                            if( result1.info( info_flags::positive ) )
                                return -2;
                            if( result1 == 0 )
                                return -4;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2.info( info_flags::nonnegative ) )
                                return -1;
                            if( result2.info( info_flags::negative ) )
                                return 1;
                            return 0;
                        }
                        default:
                            return 0;
                    }
                }
                case GREATER:
                {
                    switch( _constraintA->relation() )
                    {
                        case EQ:
                        {
                            ex result1 = lhsA - lhsB;
                            normalize( result1 );
                            if( result1.info( info_flags::negative ) )
                                return 1;
                            if( result1.info( info_flags::nonnegative ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2 == 0 )
                                return -2;
                            if( result2.info( info_flags::negative ) )
                                return -2;
                            if( result2.info( info_flags::positive ) )
                                return 1;
                            return 0;
                        }
                        case NEQ:
                        {
                            ex result1 = lhsA - lhsB;
                            normalize( result1 );
                            if( result1.info( info_flags::nonnegative ) )
                                return -1;
                            ex result2 = -1 * (lhsA + lhsB);
                            normalize( result2 );
                            if( result2.info( info_flags::nonnegative ) )
                                return -1;
                            return 0;
                        }
                        case LESS:
                        {
                            ex result1 = lhsA - lhsB;
                            normalize( result1 );
                            if( result1.info( info_flags::nonnegative ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2 == 0 )
                                return 2;
                            if( result2.info( info_flags::positive ) )
                                return 1;
                            if( result2.info( info_flags::negative ) )
                                return -1;
                            return 0;
                        }
                        case GREATER:
                        {
                            ex result1 = lhsA - lhsB;
                            normalize( result1 );
                            if( result1 == 0 )
                                return 2;
                            if( result1.info( info_flags::negative ) )
                                return 1;
                            if( result1.info( info_flags::positive ) )
                                return -1;
                            ex result2 = -1 * (lhsA + lhsB);
                            normalize( result2 );
                            if( result2.info( info_flags::nonnegative ) )
                                return -2;
                            return 0;
                        }
                        case LEQ:
                        {
                            ex result1 = lhsA - lhsB;
                            normalize( result1 );
                            if( result1.info( info_flags::positive ) )
                                return -2;
                            if( result1 == 0 )
                                return -4;
                            ex result2 = -1 * (lhsA + lhsB);
                            normalize( result2 );
                            if( result2.info( info_flags::nonnegative ) )
                                return -1;
                            if( result2.info( info_flags::negative ) )
                                return 1;
                            return 0;
                        }
                        case GEQ:
                        {
                            ex result1 = lhsA - lhsB;
                            normalize( result1 );
                            if( result1.info( info_flags::negative ) )
                                return 1;
                            if( result1.info( info_flags::rational ) )
                                return -1;
                            ex result2 = -1 * (lhsA + lhsB);
                            normalize( result2 );
                            if( result2.info( info_flags::positive ) )
                                return -2;
                            if( result2 == 0 )
                                return -4;
                            return 0;
                        }
                        default:
                            return 0;
                    }
                }
                case LEQ:
                {
                    switch( _constraintA->relation() )
                    {
                        case EQ:
                        {
                            ex result1 = lhsA - lhsB;
                            normalize( result1 );
                            if( result1.info( info_flags::nonnegative ) )
                                return 1;
                            if( result1.info( info_flags::negative ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2 == 0 )
                                return 1;
                            if( result2.info( info_flags::negative ) )
                                return 1;
                            if( result2.info( info_flags::positive ) )
                                return -2;
                            return 0;
                        }
                        case NEQ:
                        {
                            ex result1 = -1 * (lhsA - lhsB);
                            normalize( result1 );
                            if( result1 == 0 )
                                return -3;
                            if( result1.info( info_flags::positive ) )
                                return -1;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2 == 0 )
                                return -3;
                            if( result2.info( info_flags::positive ) )
                                return -1;
                            return 0;
                        }
                        case LESS:
                        {
                            ex result1 = lhsA - lhsB;
                            normalize( result1 );
                            if( result1.info( info_flags::negative ) )
                                return -1;
                            if( result1.info( info_flags::rational ) )
                                return 1;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2.info( info_flags::positive ) )
                                return -2;
                            if( result2 == 0 )
                                return -4;
                            return 0;
                        }
                        case GREATER:
                        {
                            ex result1 = -1 * (lhsA - lhsB);
                            normalize( result1 );
                            if( result1.info( info_flags::positive ) )
                                return -2;
                            if( result1 == 0 )
                                return -4;
                            ex result2 = -1 * (lhsA + lhsB);
                            normalize( result2 );
                            if( result2.info( info_flags::nonnegative ) )
                                return 1;
                            if( result2.info( info_flags::negative ) )
                                return -1;
                            return 0;
                        }
                        case LEQ:
                        {
                            ex result1 = lhsA - lhsB;
                            normalize( result1 );
                            if( result1 == 0 )
                                return 2;
                            if( result1.info( info_flags::negative ) )
                                return -1;
                            if( result1.info( info_flags::positive ) )
                                return 1;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2 == 0 )
                                return -3;
                            if( result2.info( info_flags::positive ) )
                                return -2;
                            return 0;
                        }
                        case GEQ:
                        {
                            ex result1 = lhsA - lhsB;
                            normalize( result1 );
                            if( result1 == 0 )
                                return -3;
                            if( result1.info( info_flags::negative ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2 == 0 )
                                return 2;
                            if( result2.info( info_flags::positive ) )
                                return -1;
                            if( result2.info( info_flags::negative ) )
                                return 1;
                            return 0;
                        }
                        default:
                            return 0;
                    }
                }
                case GEQ:
                {
                    switch( _constraintA->relation() )
                    {
                        case EQ:
                        {
                            ex result1 = -1 * (lhsA - lhsB);
                            normalize( result1 );
                            if( result1.info( info_flags::nonnegative ) )
                                return 1;
                            if( result1.info( info_flags::negative ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2.info( info_flags::negative ) )
                                return -2;
                            if( result2.info( info_flags::nonnegative ) )
                                return 1;
                            return 0;
                        }
                        case NEQ:
                        {
                            ex result1 = lhsA - lhsB;
                            normalize( result1 );
                            if( result1 == 0 )
                                return -3;
                            if( result1.info( info_flags::positive ) )
                                return -1;
                            ex result2 = -1 * (lhsA + lhsB);
                            normalize( result2 );
                            if( result2 == 0 )
                                return -3;
                            if( result2.info( info_flags::positive ) )
                                return -1;
                            return 0;
                        }
                        case LESS:
                        {
                            ex result1 = lhsA - lhsB;
                            normalize( result1 );
                            if( result1.info( info_flags::positive ) )
                                return -2;
                            if( result1 == 0 )
                                return -4;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2.info( info_flags::nonnegative ) )
                                return 1;
                            if( result2.info( info_flags::negative ) )
                                return -1;
                            return 0;
                        }
                        case GREATER:
                        {
                            ex result1 = lhsA - lhsB;
                            normalize( result1 );
                            if( result1.info( info_flags::positive ) )
                                return -1;
                            if( result1.info( info_flags::rational ) )
                                return 1;
                            ex result2 = -1 * (lhsA + lhsB);
                            normalize( result2 );
                            if( result2.info( info_flags::positive ) )
                                return -2;
                            if( result2 == 0 )
                                return -4;
                            return 0;
                        }
                        case LEQ:
                        {
                            ex result1 = lhsA - lhsB;
                            normalize( result1 );
                            if( result1 == 0 )
                                return -3;
                            if( result1.info( info_flags::positive ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2 == 0 )
                                return 2;
                            if( result2.info( info_flags::positive ) )
                                return 1;
                            if( result2.info( info_flags::negative ) )
                                return -1;
                            return 0;
                        }
                        case GEQ:
                        {
                            ex result1 = lhsA - lhsB;
                            normalize( result1 );
                            if( result1 == 0 )
                                return 2;
                            if( result1.info( info_flags::negative ) )
                                return 1;
                            if( result1.info( info_flags::positive ) )
                                return -1;
                            ex result2 = lhsA + lhsB;
                            normalize( result2 );
                            if( result2 == 0 )
                                return -3;
                            if( result2.info( info_flags::negative ) )
                                return -2;
                            return 0;
                        }
                        default:
                            return 0;
                    }
                }
                default:
                    return 0;
            }
        }
        else
        {
            return 0;
        }
    }

    /**
     * Merges the two given constraints. The first constraint will be changed accordingly
     * if possible. (Assumption: This constraint OR the given constraint have to hold.)
     *
     * @param _constraintA  The first constraint to merge.
     * @param _constraintB  The second constraint to merge.
     *
     * @return
     */
    const Constraint* Constraint::mergeConstraints( const Constraint* _constraintA, const Constraint* _constraintB )
    {
        symtab::const_iterator var1 = _constraintA->variables().begin();
        symtab::const_iterator var2 = _constraintB->variables().begin();
        while( var1 != _constraintA->variables().end() && var2 != _constraintB->variables().end() )
        {
            if( strcmp( var1->first.c_str(), var2->first.c_str() ) == 0 )
            {
                var1++;
                var2++;
            }
            else
            {
                break;
            }
        }
        if( var1 == _constraintA->variables().end() && var2 == _constraintB->variables().end() )
        {
            switch( _constraintA->relation() )
            {
                case EQ:
                {
                    switch( _constraintB->relation() )
                    {
                        case EQ:
                        {
                            return NULL;
                        }
                        case NEQ:
                        {
                            ex result1 = _constraintA->mLhs - _constraintB->mLhs;
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return Formula::newConstraint( 0, EQ, symtab() );
                            }
                            ex result2 = _constraintA->mLhs + _constraintB->mLhs;
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( 0, EQ, symtab() );
                            }
                            return NULL;
                        }
                        case LESS:
                        {
                            ex result1 = _constraintA->mLhs - _constraintB->mLhs;
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return Formula::newConstraint( _constraintA->mLhs, LEQ, _constraintA->variables() );
                            }
                            ex result2 = _constraintA->mLhs + _constraintB->mLhs;
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( _constraintA->mLhs, GEQ, _constraintA->variables() );
                            }
                            return NULL;
                        }
                        case GREATER:
                        {
                            ex result1 = _constraintA->mLhs - _constraintB->mLhs;
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return Formula::newConstraint( _constraintA->mLhs, GEQ, _constraintA->variables() );
                            }
                            ex result2 = _constraintA->mLhs + _constraintB->mLhs;
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( _constraintA->mLhs, LEQ, _constraintA->variables() );
                            }
                            return NULL;
                        }
                        case LEQ:
                        {
                            ex result1 = _constraintA->mLhs - _constraintB->mLhs;
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return Formula::newConstraint( _constraintA->mLhs, LEQ, _constraintA->variables() );
                            }
                            ex result2 = _constraintA->mLhs + _constraintB->mLhs;
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( _constraintA->mLhs, GEQ, _constraintA->variables() );
                            }
                            return NULL;
                        }
                        case GEQ:
                        {
                            ex result1 = _constraintA->mLhs - _constraintB->mLhs;
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return Formula::newConstraint( _constraintA->mLhs, GEQ, _constraintA->variables() );
                            }
                            ex result2 = _constraintA->mLhs + _constraintB->mLhs;
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( _constraintA->mLhs, LEQ, _constraintA->variables() );
                            }
                            return NULL;
                        }
                        default:
                            return NULL;
                    }
                }
                case NEQ:
                {
                    switch( _constraintB->relation() )
                    {
                        case EQ:
                        {
                            ex result1 = _constraintA->mLhs - _constraintB->mLhs;
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return Formula::newConstraint( 0, EQ, symtab() );
                            }
                            ex result2 = _constraintA->mLhs + _constraintB->mLhs;
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( 0, EQ, symtab() );
                            }
                            return NULL;
                        }
                        case NEQ:
                        {
                            return NULL;
                        }
                        case LESS:
                        {
                            ex result1 = _constraintA->mLhs - _constraintB->mLhs;
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return _constraintA;
                            }
                            ex result2 = _constraintA->mLhs + _constraintB->mLhs;
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return _constraintA;
                            }
                            return NULL;
                        }
                        case GREATER:
                        {
                            ex result1 = _constraintA->mLhs - _constraintB->mLhs;
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return _constraintA;
                            }
                            ex result2 = _constraintA->mLhs + _constraintB->mLhs;
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return _constraintA;
                            }
                            return NULL;
                        }
                        case LEQ:
                        {
                            return NULL;
                        }
                        case GEQ:
                        {
                            return NULL;
                        }
                        default:
                            return NULL;
                    }
                }
                case LESS:
                {
                    switch( _constraintB->relation() )
                    {
                        case EQ:
                        {
                            ex result1 = _constraintA->mLhs - _constraintB->mLhs;
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return Formula::newConstraint( _constraintB->mLhs, LEQ, _constraintB->variables() );
                            }
                            ex result2 = _constraintA->mLhs + _constraintB->mLhs;
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( _constraintB->mLhs, GEQ, _constraintB->variables() );
                            }
                            return NULL;
                        }
                        case NEQ:
                        {
                            return NULL;
                        }
                        case LESS:
                        {
                            return NULL;
                        }
                        case GREATER:
                        {
                            return NULL;
                        }
                        case LEQ:
                        {
                            return NULL;
                        }
                        case GEQ:
                        {
                            return NULL;
                        }
                        default:
                            return NULL;
                    }
                }
                case GREATER:
                {
                    switch( _constraintB->relation() )
                    {
                        case EQ:
                        {
                            ex result1 = _constraintA->mLhs - _constraintB->mLhs;
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return Formula::newConstraint( _constraintB->mLhs, GEQ, _constraintB->variables() );
                            }
                            ex result2 = _constraintA->mLhs + _constraintB->mLhs;
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( _constraintB->mLhs, LEQ, _constraintB->variables() );
                            }
                            return NULL;
                        }
                        case NEQ:
                        {
                            return NULL;
                        }
                        case LESS:
                        {
                            return NULL;
                        }
                        case GREATER:
                        {
                            return NULL;
                        }
                        case LEQ:
                        {
                            return NULL;
                        }
                        case GEQ:
                        {
                            return NULL;
                        }
                        default:
                            return NULL;
                    }
                }
                case LEQ:
                {
                    switch( _constraintB->relation() )
                    {
                        case EQ:
                        {
                            ex result1 = _constraintA->mLhs - _constraintB->mLhs;
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return _constraintA;
                            }
                            ex result2 = _constraintA->mLhs + _constraintB->mLhs;
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( _constraintB->mLhs, GEQ, _constraintB->variables() );
                            }
                            return NULL;
                        }
                        case NEQ:
                        {
                            return NULL;
                        }
                        case LESS:
                        {
                            return NULL;
                        }
                        case GREATER:
                        {
                            return NULL;
                        }
                        case LEQ:
                        {
                            return NULL;
                        }
                        case GEQ:
                        {
                            return NULL;
                        }
                        default:
                            return NULL;
                    }
                }
                case GEQ:
                {
                    switch( _constraintB->relation() )
                    {
                        case EQ:
                        {
                            ex result1 = _constraintA->mLhs - _constraintB->mLhs;
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return _constraintA;
                            }
                            ex result2 = _constraintA->mLhs + _constraintB->mLhs;
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( _constraintB->mLhs, LEQ, _constraintB->variables() );
                            }
                            return NULL;
                        }
                        case NEQ:
                        {
                            return NULL;
                        }
                        case LESS:
                        {
                            return NULL;
                        }
                        case GREATER:
                        {
                            return NULL;
                        }
                        case LEQ:
                        {
                            return NULL;
                        }
                        case GEQ:
                        {
                            return NULL;
                        }
                        default:
                            return NULL;
                    }
                }
                default:
                    return NULL;
            }
        }
        else
        {
            return NULL;
        }
    }

    /**
     * Checks for redundant constraint order.
     *
     * @param _constraintA  The first constraint to merge.
     * @param _constraintB  The second constraint to merge.
     * @param _conjconstraint The third constraint to merge.
     *
     *
     * @return  true,   if (( _constraintA or _constraintB ) and _conditionconstraint) is a tautology:
     *
     *                  p>c  or p<=d     and c<=d
     *                  p>=c or p<=d     and c<=d
     *                  p>c  or p<d      and c<d
     *                  p=c  or p!=d     and c=d
     *                  p<c  or p!=d     and c>d
     *                  p>c  or p!=d     and c<d
     *                  p<=c or p!=d     and c>=d
     *                  p>=c or p!=d     and c<=d
     *
     *          false,  otherwise.
     */
    bool Constraint::combineConstraints( const Constraint* _constraintA, const Constraint* _constraintB, const Constraint* _conditionconstraint )
    {
        symtab::const_iterator var1 = _constraintA->variables().begin();
        symtab::const_iterator var2 = _constraintB->variables().begin();
        symtab::const_iterator var3 = _conditionconstraint->variables().begin();
        // Checks if the three constraints are paarwise different from each other
        while( var1 != _constraintA->variables().end() && var2 != _constraintB->variables().end() )
        {
            if( strcmp( var1->first.c_str(), var2->first.c_str() ) == 0 )
            {
                var1++;
                var2++;
            }
            else
            {
                return false;
            }
        }
        var1 = _constraintA->variables().begin();
        var2 = _constraintB->variables().begin();
        while( var1 != _constraintA->variables().end() && var3 != _conditionconstraint->variables().end() )
        {
            if( strcmp( var1->first.c_str(), var3->first.c_str() ) == 0 )
            {
                var1++;
                var3++;
            }
            else
            {
                return false;
            }
        }
        var1 = _constraintA->variables().begin();
        var3 = _conditionconstraint->variables().begin();
        while( var2 != _constraintB->variables().end() && var3 != _conditionconstraint->variables().end() )
        {
            if( strcmp( var2->first.c_str(), var3->first.c_str() ) == 0 )
            {
                var2++;
                var3++;
            }
            else
            {
                return false;
            }
        }
        // If all constraints are different check if disjunction is redundant
        switch( _constraintA->relation() )
        {
            case EQ:
            {
                if( _constraintB->relation() == NEQ )
                {
                    if( _conditionconstraint->relation() == EQ )
                    {
                        // Case: ( p = c or p != d ) and c = d
                        ex result = _constraintA->mLhs - _constraintB->mLhs + _conditionconstraint->mLhs;
                        normalize( result );
                        if( result == 0 )
                            return true;
                        result = _constraintA->mLhs - _constraintB->mLhs - _conditionconstraint->mLhs;
                        normalize( result );
                        if( result == 0 )
                            return true;
                        result = _constraintA->mLhs + _constraintB->mLhs + _conditionconstraint->mLhs;
                        normalize( result );
                        if( result == 0 )
                            return true;
                        result = _constraintA->mLhs + _constraintB->mLhs - _conditionconstraint->mLhs;
                        normalize( result );
                        if( result == 0 )
                            return true;
                    }
                }
                return false;
            }
            case NEQ:
            {
                switch( _constraintB->relation() )
                {
                    case EQ:
                    {
                        if( _conditionconstraint->relation() == EQ )
                        {
                            // Case: ( p != c or p = d ) and c = d
                            ex result = _constraintA->mLhs - _constraintB->mLhs + _conditionconstraint->mLhs;
                            normalize( result );
                            if( result == 0 )
                                return true;
                            result = _constraintA->mLhs - _constraintB->mLhs - _conditionconstraint->mLhs;
                            normalize( result );
                            if( result == 0 )
                                return true;
                            result = _constraintA->mLhs + _constraintB->mLhs + _conditionconstraint->mLhs;
                            normalize( result );
                            if( result == 0 )
                                return true;
                            result = _constraintA->mLhs + _constraintB->mLhs - _conditionconstraint->mLhs;
                            normalize( result );
                            if( result == 0 )
                                return true;
                        }
                        return false;
                    }
                    case LESS:
                    {
                        // Case: ( p != d or p < c ) and c > d
                        // or      ( p != d or p < c ) and c < d
                        switch( _conditionconstraint->relation() )
                        {
                            case LESS:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA->mLhs + _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case GREATER:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA->mLhs - _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            default:
                                return false;
                        }
                    }
                    case GREATER:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case LESS:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA->mLhs + _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case GREATER:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA->mLhs - _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            default:
                                return false;
                        }
                    }
                    case LEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case LEQ:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA->mLhs + _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case GEQ:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA->mLhs - _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            default:
                                return false;
                        }
                    }
                    case GEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case LEQ:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA->mLhs - _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case GEQ:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA->mLhs + _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            default:
                                return false;
                        }
                    }
                    default:
                        return false;
                }
            }
            case LESS:
            {
                switch( _constraintB->relation() )
                {
                    case NEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case LESS:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA->mLhs + _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case GREATER:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA->mLhs - _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            default:
                                return false;
                        }
                    }
                    case LESS:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case LESS:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case GREATER:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            default:
                                return false;
                        }
                    }
                    case GREATER:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case LESS:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case GREATER:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            default:
                                return false;
                        }
                    }
                    case LEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case LEQ:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case GEQ:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            default:
                                return false;
                        }
                    }
                    case GEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case LEQ:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case GEQ:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            default:
                                return false;
                        }
                    }
                    default:
                        return false;
                }
            }
            case GREATER:
            {
                switch( _constraintB->relation() )
                {
                    case NEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case LESS:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA->mLhs + _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case GREATER:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA->mLhs - _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            default:
                                return false;
                        }
                    }
                    case LESS:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case LESS:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case GREATER:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            default:
                                return false;
                        }
                    }
                    case GREATER:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case LESS:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case GREATER:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            default:
                                return false;
                        }
                    }
                    case LEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case LEQ:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case GEQ:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            default:
                                return false;
                        }
                    }
                    case GEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case LEQ:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case GEQ:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            default:
                                return false;
                        }
                    }
                    default:
                        return false;
                }
            }
            case LEQ:
            {
                switch( _constraintB->relation() )
                {
                    case NEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case LEQ:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA->mLhs + _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case GEQ:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA->mLhs - _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            default:
                                return false;
                        }
                    }
                    case LESS:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case LEQ:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case GEQ:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            default:
                                return false;
                        }
                    }
                    case GREATER:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case LEQ:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case GEQ:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            default:
                                return false;
                        }
                    }
                    case LEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case LEQ:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case GEQ:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            default:
                                return false;
                        }
                    }
                    case GEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case LEQ:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case GEQ:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            default:
                                return false;
                        }
                    }
                    default:
                        return false;
                }
            }
            case GEQ:
            {
                switch( _constraintB->relation() )
                {
                    case NEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case LEQ:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA->mLhs - _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case GEQ:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA->mLhs + _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            default:
                                return false;
                        }
                    }
                    case LESS:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case LEQ:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case GEQ:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            default:
                                return false;
                        }
                    }
                    case GREATER:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case LEQ:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case GEQ:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            default:
                                return false;
                        }
                    }
                    case LEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case LEQ:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case GEQ:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            default:
                                return false;
                        }
                    }
                    case GEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case LEQ:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case GEQ:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            default:
                                return false;
                        }
                    }
                    default:
                        return false;
                }
            }
            default:
                return false;
        }
    }
}    // namespace smtrat

