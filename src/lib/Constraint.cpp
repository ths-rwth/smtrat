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
        const map<unsigned, Polynomial>& coeffs = mVarInfoMap.getVarInfo( _var )->coeffs();
        auto expCoeffPair = coeffs.find( _degree );
        if( expCoeffPair != coeffs.end() )
        {
            return expCoeffPair->second;
        }
        return Polynomial( Rational( 0 ) );
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
//        mVarInfoMap( mLhs.getVarInfo<false>() ); //TODO: implement this line
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
                    else if( _unequalSwitch == 1 )
                    {
                        string lhsString = mLhs.toString( false, _friendlyVarNames );
                        return "(or (< " + lhsString + " 0) (> " + lhsString + " 0))";
                    }
                    else
                    {
                        string lhsString = mLhs.toString( false, _friendlyVarNames );
                        return "(not (= " + lhsString + " 0))";
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
        result += (_infix ? "0" : (" " + mLhs.toString( false, _friendlyVarNames ) + " 0)"));
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
        for( auto var = mVariables.begin(); var != mVariables.end(); ++var )
        {
            auto varInfo = mVarInfoMap.getVarInfo( *var );
            _out << "        " << varToString( *var, _friendlyVarNames ) << " has " << varInfo->occurence() << " occurences." << endl;
            _out << "        " << varToString( *var, _friendlyVarNames ) << " has the maximal degree of " << varInfo->maxDegree() << "." << endl;
            _out << "        " << varToString( *var, _friendlyVarNames ) << " has the minimal degree of " << varInfo->minDegree() << "." << endl;
        }
    }
    
    static const signed A_IFF_B = 2;
    static const signed A_IMPLIES_B = 1;
    static const signed B_IMPLIES_A = -1;
    static const signed NOT__A_AND_B = -2;
    static const signed A_AND_B__IFF_C = -3;
    static const signed A_XOR_B = -4;

    /**
     * Compares _constraintA with _constraintB.
     *
     * @return  2, if it is easy to decide that _constraintA and _constraintB have the same solutions. _constraintA = _constraintB
     *           1, if it is easy to decide that _constraintB includes all solutions of _constraintA;   _constraintA -> _constraintB
     *          -1, if it is easy to decide that _constraintA includes all solutions of _constraintB;   _constraintB -> _constraintA
     *          -2, if it is easy to decide that _constraintA has no solution common with _constraintB; not(_constraintA and _constraintB)
     *          -3, if it is easy to decide that _constraintA and _constraintB can be intersected;      _constraintA and _constraintB = _constraintC
     *          -4, if it is easy to decide that _constraintA is the inverse of _constraintB;           _constraintA xor _constraintB
     *           0, otherwise.
     */
    signed Constraint::compare( const Constraint* _constraintA, const Constraint* _constraintB )
    {
        /*
         * Check whether it holds that 
         * 
         *                      _constraintA  =  a_1*m_1+...+a_k*m_k + c ~ 0
         * and 
         *                      _constraintB  =  b_1*m_1+...+b_k*m_k + d ~ 0, 
         * 
         * where a_1,..., a_k, b_1,..., b_k, c, d are rational coefficients, 
         *       m_1,..., m_k are non-constant monomials and 
         *       exists a rational g such that 
         * 
         *                   a_i = g * b_i for all 1<=i<=k 
         *              or   b_i = g * a_i for all 1<=i<=k 
         */
        auto termA = _constraintA->lhs().begin();
        auto termB = _constraintB->lhs().begin();
        assert( !(*termA)->isZero() );
        Rational g;
        Rational termAcoeffAbs = cln::abs( (*termA)->coeff() );
        Rational termBcoeffAbs = cln::abs( (*termB)->coeff() );
        bool termACoeffGreater = termAcoeffAbs > termBcoeffAbs; 
        bool termBCoeffGreater = termAcoeffAbs < termBcoeffAbs;
        if( termACoeffGreater ) g = (*termA)->coeff()/(*termB)->coeff();
        else if( termBCoeffGreater ) g = (*termB)->coeff()/(*termA)->coeff();
        else if( (*termA)->coeff() == (*termB)->coeff() ) g = Rational( 1 );
        else
        {
            g = Rational( -1 );
            termBCoeffGreater = true;
        }
        Rational c = 0;
        Rational d = 0;
        ++termA;
        ++termB;
        while( termA != _constraintA->lhs().end() && termB != _constraintB->lhs().end() )
        {
            if( (*termA)->isConstant() || (*termB)->isConstant() )
            {
                if( (*termA)->isConstant() )
                {
                    c = (termBCoeffGreater ? (*termA)->coeff() * g : (*termA)->coeff());
                    ++termA;
                }
                if( (*termB)->isConstant() )
                {
                    d = (termACoeffGreater ? (*termB)->coeff() * g : (*termB)->coeff());
                    ++termB;
                }
                assert( termA == _constraintA->lhs().end() && termB == _constraintB->lhs().end() );
            }
            else if( *(*termA)->monomial() != *(*termB)->monomial() ) return 0;
            else if( termACoeffGreater )
            {
                if( (*termA)->coeff() != g * (*termB)->coeff() ) return 0;
            }
            else if( termBCoeffGreater )
            {
                if( g * (*termA)->coeff() != (*termB)->coeff() ) return 0;
            }
            else if( (*termA)->coeff() != g * (*termB)->coeff() ) return 0;
            ++termA;
            ++termB;
        }
        Relation relA = _constraintA->relation();
        Relation relB = _constraintB->relation();
        if( g < 0 )
        {
            switch( (termACoeffGreater ? relA : relB ) )
            {
                case LEQ:
                    if( termACoeffGreater ) relA = GEQ; 
                    else relB = GEQ;
                    break;
                case GEQ:
                    if( termACoeffGreater ) relA = LEQ; 
                    else relB = LEQ;
                    break;
                case LESS:
                    if( termACoeffGreater ) relA = GREATER;
                    else relB = GREATER;
                    break;
                case GREATER:
                    if( termACoeffGreater )  relA = LESS;
                    else relB = LESS;
                    break;
                default:
                    break;
            }
        }
        switch( relB )
        {
            case EQ:
                switch( relA )
                {
                    case EQ: // p+c=0  and  p+d=0
                        if( c == d ) return A_IFF_B; 
                        else return NOT__A_AND_B;
                    case NEQ: // p+c!=0  and  p+d=0
                        if( c == d ) return A_XOR_B;
                        else return B_IMPLIES_A;
                    case LESS: // p+c<0  and  p+d=0
                        if( c < d ) return B_IMPLIES_A;
                        else return NOT__A_AND_B;
                    case GREATER: // p+c>0  and  p+d=0
                        if( c > d ) return B_IMPLIES_A;
                        else return NOT__A_AND_B;
                    case LEQ: // p+c<=0  and  p+d=0
                        if( c <= d ) return B_IMPLIES_A;
                        else return NOT__A_AND_B;
                    case GEQ: // p+c>=0  and  p+d=0
                        if( c >= d ) return B_IMPLIES_A;
                        else return NOT__A_AND_B;
                    default:
                        return false;
                }
            case NEQ:
                switch( relA )
                {
                    case EQ: // p+c=0  and  p+d!=0
                        if( c == d ) return A_XOR_B;
                        else return A_IMPLIES_B;
                    case NEQ: // p+c!=0  and  p+d!=0
                        if( c == d ) return A_IFF_B;
                        else return 0;
                    case LESS: // p+c<0  and  p+d!=0
                        if( c >= d ) return A_IMPLIES_B;
                        else return 0;
                    case GREATER: // p+c>0  and  p+d!=0
                        if( c <= d ) return A_IMPLIES_B;
                        else return 0;
                    case LEQ: // p+c<=0  and  p+d!=0
                        if( c > d ) return A_IMPLIES_B;
                        else if( c == d ) return A_AND_B__IFF_C;
                        else return 0;
                    case GEQ: // p+c>=0  and  p+d!=0
                        if( c < d ) return A_IMPLIES_B;
                        else if( c == d ) return A_AND_B__IFF_C;
                        else return 0;
                    default:
                        return 0;
                }
            case LESS:
                switch( relA )
                {
                    case EQ: // p+c=0  and  p+d<0
                        if( c > d ) return A_IMPLIES_B;
                        else return NOT__A_AND_B;
                    case NEQ: // p+c!=0  and  p+d<0
                        if( c <= d ) return B_IMPLIES_A;
                        else return 0;
                    case LESS: // p+c<0  and  p+d<0
                        if( c == d ) return A_IFF_B;
                        else if( c < d ) return B_IMPLIES_A;
                        else return A_IMPLIES_B;
                    case GREATER: // p+c>0  and  p+d<0
                        if( c <= d ) return NOT__A_AND_B;
                        else return 0;
                    case LEQ: // p+c<=0  and  p+d<0
                        if( c > d ) return A_IMPLIES_B;
                        else return B_IMPLIES_A;
                    case GEQ: // p+c>=0  and  p+d<0
                        if( c < d ) return NOT__A_AND_B;
                        else if( c == d ) return A_XOR_B;
                        else return 0;
                    default:
                        return 0;
                }
            case GREATER:
            {
                switch( relA )
                {
                    case EQ: // p+c=0  and  p+d>0
                        if( c < d ) return A_IMPLIES_B;
                        else return NOT__A_AND_B;
                    case NEQ: // p+c!=0  and  p+d>0
                        if( c >= d ) return B_IMPLIES_A;
                        else return 0;
                    case LESS: // p+c<0  and  p+d>0
                        if( c >= d ) return NOT__A_AND_B;
                        else return 0;
                    case GREATER: // p+c>0  and  p+d>0
                        if( c == d ) return A_IFF_B;
                        else if( c > d ) return B_IMPLIES_A;
                        else return A_IMPLIES_B;
                    case LEQ: // p+c<=0  and  p+d>0
                        if( c > d ) return NOT__A_AND_B;
                        else if( c == d ) return A_XOR_B;
                        else return 0;
                    case GEQ: // p+c>=0  and  p+d>0
                        if( c > d ) return B_IMPLIES_A;
                        else return A_IMPLIES_B;
                    default:
                        return 0;
                }
            }
            case LEQ:
            {
                switch( relA )
                {
                    case EQ: // p+c=0  and  p+d<=0
                        if( c >= d ) return A_IMPLIES_B;
                        else return NOT__A_AND_B;
                    case NEQ: // p+c!=0  and  p+d<=0
                        if( c < d ) return B_IMPLIES_A;
                        else if( c == d ) return A_AND_B__IFF_C;
                        else return 0;
                    case LESS: // p+c<0  and  p+d<=0
                        if( c < d ) return B_IMPLIES_A;
                        else return A_IMPLIES_B;
                    case GREATER: // p+c>0  and  p+d<=0
                        if( c > d ) return NOT__A_AND_B;
                        else if( c == d ) return A_XOR_B;
                        else return 0;
                    case LEQ: // p+c<=0  and  p+d<=0
                        if( c == d ) return A_IFF_B;
                        else if( c < d ) return B_IMPLIES_A;
                        else return A_IMPLIES_B;
                    case GEQ: // p+c>=0  and  p+d<=0
                        if( c < d ) return NOT__A_AND_B;
                        else if( c == d ) return A_AND_B__IFF_C;
                        else return 0;
                    default:
                        return 0;
                }
            }
            case GEQ:
            {
                switch( relA )
                {
                    case EQ: // p+c=0  and  p+d>=0
                        if( c <= d ) return A_IMPLIES_B;
                        else return NOT__A_AND_B;
                    case NEQ: // p+c!=0  and  p+d>=0
                        if( c > d ) return B_IMPLIES_A;
                        else if( c == d ) return A_AND_B__IFF_C;
                        else return 0;
                    case LESS: // p+c<0  and  p+d>=0
                        if( c > d ) return NOT__A_AND_B;
                        else if( c == d ) return A_XOR_B;
                        else return 0;
                    case GREATER: // p+c>0  and  p+d>=0
                        if( c < d ) return B_IMPLIES_A;
                        else return A_IMPLIES_B;
                    case LEQ: // p+c<=0  and  p+d>=0
                        if( c > d ) return NOT__A_AND_B;
                        else if( c == d ) return A_AND_B__IFF_C;
                        else return 0;
                    case GEQ: // p+c>=0  and  p+d>=0
                        if( c == d ) return A_IFF_B;
                        else if( c < d ) return A_IMPLIES_B;
                        else return B_IMPLIES_A;
                    default:
                        return 0;
                }
            }
            default:
                return 0;
        }
    }
}    // namespace smtrat

