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

#include <ginacra/DoubleInterval.h>

#include "Constraint.h"
#include "ConstraintPool.h"
#include "Formula.h"

using namespace std;
using namespace GiNaC;

namespace smtrat
{
    const unsigned MAX_DEGREE_FOR_FACTORIZATION = 40;
    const unsigned MIN_DEGREE_FOR_FACTORIZATION = 2;
    const unsigned MAX_DIMENSION_FOR_FACTORIZATION = 6;
    const unsigned MAX_NUMBER_OF_MONOMIALS_FOR_FACTORIZATION = 300;

    recursive_mutex Constraint::mMutex;

    Constraint::Constraint():
        mID( 0 ),
        mSecondHash( CR_EQ ),
        mIsNeverPositive( false ),
        mIsNeverNegative( false ),
        mIsNeverZero( false ),
        mContainsRealValuedVariables( false ),
        mContainsIntegerValuedVariables( false ),
        mNumMonomials( 0 ),
        mMaxMonomeDegree( 0 ),
        mMinMonomeDegree( 0 ),
        mRelation( CR_EQ ),
        mLhs( 0 ),
        mMultiRootLessLhs( 0 ),
        mFactorization( 0 ),
        mpCoefficients( new Coefficients() ),
        mVariables(),
        mVarInfoMap()
    {
        mFirstHash = mLhs.gethash();
    }

    Constraint::Constraint( const GiNaC::ex& _lhs, const Constraint_Relation _cr, const symtab& _variables, unsigned _id ):
        mID( _id ),
        mFirstHash( _lhs.gethash() ),
        mSecondHash( _cr ),
        mIsNeverPositive( false ),
        mIsNeverNegative( false ),
        mIsNeverZero( false ),
        mContainsRealValuedVariables( false ),
        mContainsIntegerValuedVariables( false ),
        mNumMonomials( 0 ),
        mMaxMonomeDegree( 0 ),
        mMinMonomeDegree( 0 ),
        mRelation( _cr ),
        mLhs( _lhs ),
        mMultiRootLessLhs( 0 ),
        mFactorization( 0 ),
        mpCoefficients( new Coefficients() ),
        mVariables(),
        mVarInfoMap()
    {
        for( auto var = _variables.begin(); var != _variables.end(); ++var )
        {
            if( mLhs.has( var->second ) )
            {
                mVariables.insert( *var );
                Variable_Domain varDom = Formula::domain( var->second );
                mContainsRealValuedVariables = (varDom == REAL_DOMAIN);
                mContainsIntegerValuedVariables = (varDom == INTEGER_DOMAIN);
            }
        }
        assert( !mVariables.empty() || _lhs.info( info_flags::rational ) );
    }

    Constraint::Constraint( const Constraint& _constraint, bool _rehash ):
        mID( _constraint.id() ),
        mFirstHash( _rehash ? _constraint.mLhs.gethash() : _constraint.firstHash() ),
        mSecondHash( _rehash ? _constraint.relation() : _constraint.secondHash() ),
        mIsNeverPositive( _constraint.mIsNeverPositive ),
        mIsNeverNegative( _constraint.mIsNeverNegative ),
        mIsNeverZero( _constraint.mIsNeverZero ),
        mContainsRealValuedVariables( _constraint.mContainsRealValuedVariables ),
        mContainsIntegerValuedVariables( _constraint.mContainsIntegerValuedVariables ),
        mNumMonomials( _constraint.mNumMonomials ),
        mMaxMonomeDegree( _constraint.mMaxMonomeDegree ),
        mMinMonomeDegree( _constraint.mMinMonomeDegree ),
        mRelation( _constraint.relation() ),
        mLhs( _constraint.mLhs ),
        mMultiRootLessLhs( _constraint.mMultiRootLessLhs ),
        mFactorization( _constraint.mFactorization ),
        mpCoefficients( new Coefficients( *_constraint.mpCoefficients ) ),
        mVariables( _constraint.variables() ),
        mVarInfoMap( _constraint.mVarInfoMap )
    {}

    Constraint::~Constraint()
    {
        delete mpCoefficients;
    }

    /**
     * @param _variableName The name of the variable we search for.
     * @param _variable     The according variable.
     *
     * @return true,    if the variable occurs in this constraint;
     *         false,   otherwise.
     */
    bool Constraint::variable( const string& _variableName, symbol& _variable ) const
    {
        symtab::const_iterator var = variables().find( _variableName );
        if( var != variables().end() )
        {
            _variable = ex_to<symbol>( var->second );
            return true;
        }
        else
        {
            return false;
        }
    }

    /**
     * Checks if the variable corresponding to the given variable name occurs in the constraint.
     *
     * @param _varName  The name of the variable.
     *
     * @return  true    , if the given variable occurs in the constraint;
     *          false   , otherwise.
     */
    bool Constraint::hasVariable( const std::string& _varName ) const
    {
        for( symtab::const_iterator var = variables().begin(); var != variables().end(); ++var )
        {
            if( var->first == _varName )
                return true;
        }
        return false;
    }

    /**
     * Checks whether the given value satisfies the given relation to zero.
     *
     * @param _value The value to compare with zero.
     * @param _relation The relation between the given value and zero.
     * @return True,  if the given value satisfies the given relation to zero;
     *         False, otherwise.
     */
    bool Constraint::evaluate( const numeric& _value, Constraint_Relation _relation )
    {
        switch( _relation )
        {
            case CR_EQ:
            {
                if( _value == 0 ) return true;
                else return false;
            }
            case CR_NEQ:
            {
                if( _value == 0 ) return false;
                else return true;
            }
            case CR_LESS:
            {
                if( _value < 0 ) return true;
                else return false;
            }
            case CR_GREATER:
            {
                if( _value > 0 ) return true;
                else return false;
            }
            case CR_LEQ:
            {
                if( _value <= 0 ) return true;
                else return false;
            }
            case CR_GEQ:
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
     *         1, if the constraint is consistent.
     *         2, if the constraint still contains variables.
     */
    unsigned Constraint::isConsistent() const
    {
        if( variables().empty() )
        {
            return evaluate( ex_to<numeric>( mLhs ), relation() ) ? 1 : 0;
        }
        else
        {
            switch( relation() )
            {
                case CR_EQ:
                {
                    if( mIsNeverZero ) return 0;
                    break;
                }
                case CR_NEQ:
                {
                    if( mIsNeverZero ) return 1;
                    break;
                }
                case CR_LESS:
                {
                    if( mIsNeverZero && mIsNeverPositive ) return 1;
                    if( mIsNeverNegative ) return 0;
                    break;
                }
                case CR_GREATER:
                {
                    if( mIsNeverZero && mIsNeverNegative ) return 1;
                    if( mIsNeverPositive ) return 0;
                    break;
                }
                case CR_LEQ:
                {
                    if( mIsNeverPositive ) return 1;
                    if( mIsNeverZero && mIsNeverNegative ) return 0;
                    break;
                }
                case CR_GEQ:
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
    unsigned Constraint::consistentWith( const GiNaCRA::evaldoubleintervalmap& _solutionInterval ) const
    {
//        cout << *this << " consistent with" << endl;
//        for( auto iter = _solutionInterval.begin(); iter != _solutionInterval.end(); ++iter )
//        {
//            cout << "   " << ex( iter->first ) << " in " << iter->second << endl;
//        }
        if( variables().empty() )
        {
//            cout << (evaluate( ex_to<numeric>( mLhs ), relation() ) ? 1 : 0) << endl;
            return evaluate( ex_to<numeric>( mLhs ), relation() ) ? 1 : 0;
        }
        else
        {
            GiNaCRA::DoubleInterval solutionSpace = GiNaCRA::DoubleInterval::evaluate( mLhs, _solutionInterval );
            if( solutionSpace.empty() )
            {
//                cout << 2 << endl;
                return 2;
            }
            switch( relation() )
            {
                case CR_EQ:
                {
                    if( solutionSpace.diameter() == 0 && solutionSpace.left() == 0 )
                    {
//                        cout << 1 << endl;
                        return 1;
                    }
                    else if( !solutionSpace.contains( 0 ) )
                    {
//                        cout << 0 << endl;
                        return 0;
                    }
                    break;
                }
                case CR_NEQ:
                {
                    if( !solutionSpace.contains( 0 ) )
                    {
//                        cout << 1 << endl;
                        return 1;
                    }
                    break;
                }
                case CR_LESS:
                {
                    if( solutionSpace.rightType() != GiNaCRA::DoubleInterval::INFINITY_BOUND )
                    {
                        if( solutionSpace.right() < 0 )
                        {
//                            cout << 1 << endl;
                            return 1;
                        }
                        else if( solutionSpace.right() == 0 && solutionSpace.rightType() == GiNaCRA::DoubleInterval::STRICT_BOUND ) return 1;
                    }
                    if( solutionSpace.leftType() != GiNaCRA::DoubleInterval::INFINITY_BOUND )
                    {
                        if( solutionSpace.left() >= 0 )
                        {
//                            cout << 0 << endl;
                            return 0;
                        }
                    }
                    break;
                }
                case CR_GREATER:
                {
                    if( solutionSpace.leftType() != GiNaCRA::DoubleInterval::INFINITY_BOUND )
                    {
                        if( solutionSpace.left() > 0 )
                        {
//                            cout << 1 << endl;
                            return 1;
                        }
                        else if( solutionSpace.left() == 0 && solutionSpace.leftType() == GiNaCRA::DoubleInterval::STRICT_BOUND )
                        {
//                            cout << 1 << endl;
                            return 1;
                        }
                    }
                    if( solutionSpace.rightType() != GiNaCRA::DoubleInterval::INFINITY_BOUND )
                    {
                        if( solutionSpace.right() <= 0 )
                        {
//                            cout << 0 << endl;
                            return 0;
                        }
                    }
                    break;
                }
                case CR_LEQ:
                {
                    if( solutionSpace.rightType() != GiNaCRA::DoubleInterval::INFINITY_BOUND )
                    {
                        if( solutionSpace.right() <= 0 )
                        {
//                            cout << 1 << endl;
                            return 1;
                        }
                    }
                    if( solutionSpace.leftType() != GiNaCRA::DoubleInterval::INFINITY_BOUND )
                    {
                        if( solutionSpace.left() > 0 )
                        {
//                            cout << 0 << endl;
                            return 0;
                        }
                        else if( solutionSpace.left() == 0 && solutionSpace.leftType() == GiNaCRA::DoubleInterval::STRICT_BOUND )
                        {
//                            cout << 0 << endl;
                            return 0;
                        }
                    }
                    break;
                }
                case CR_GEQ:
                {
                    if( solutionSpace.leftType() != GiNaCRA::DoubleInterval::INFINITY_BOUND )
                    {
                        if( solutionSpace.left() >= 0 )
                        {
//                            cout << 1 << endl;
                            return 1;
                        }
                    }
                    if( solutionSpace.rightType() != GiNaCRA::DoubleInterval::INFINITY_BOUND )
                    {
                        if( solutionSpace.right() < 0 )
                        {
//                            cout << 0 << endl;
                            return 0;
                        }
                        else if( solutionSpace.right() == 0 && solutionSpace.rightType() == GiNaCRA::DoubleInterval::STRICT_BOUND )
                        {
//                            cout << 0 << endl;
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
//            cout << 2 << endl;
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
    unsigned Constraint::satisfiedBy( exmap& _assignment ) const
    {
        ex tmp = mLhs.subs( _assignment );
        if( is_exactly_a<numeric>( tmp ) )
        {
            return evaluate( ex_to<numeric>( tmp ), relation() ) ? 1 : 0;
        }
        else return 2;
    }

    /**
     * Checks whether the constraints solutions for the given variable are finitely many (at least one).
     *
     * @param _variableName The variable for which the method detects, whether it is linear.
     *
     * @return  true,   if the constraints solutions for the given variable are finitely many (at least one);
     *          false,  otherwise.
     */
    bool Constraint::hasFinitelyManySolutionsIn( const std::string& _variableName ) const
    {
        if( relation() != CR_EQ )
        {
            return false;
        }
        else
        {
            symtab::const_iterator var = variables().find( _variableName );
            if( var != variables().end() )
            {
                for( unsigned i = maxDegree( var->second ); i > 0; --i )
                {
                    if( !coefficient( var->second, i ).info( info_flags::rational ) )
                    {
                        return false;
                    }
                }
                return true;
            }
            else
            {
                return false;
            }
        }
    }

    /**
     * Calculates the coefficient of the given variable with the given degree. Note, that it only
     * computes the coefficient once and stores the result.
     *
     * @param _variable The variable for which to calculate the coefficient.
     * @param _degree The according degree of the variable for which to calculate the coefficient.
     * @return The ith coefficient of the given variable, where i is the given degree.
     */
    ex Constraint::coefficient( const ex& _variable, int _degree ) const
    {
        #ifdef SMTRAT_STRAT_PARALLEL_MODE
        VarDegree vd = VarDegree( _variable, _degree );
        Coefficients::const_iterator coeffIter = mpCoefficients->find( vd );
        if( coeffIter != mpCoefficients->end() )
        {
            return coeffIter->second;
        }
        else
        {
            assert( _degree > (signed) maxDegree( _variable ) );
            return ex( 0 );
        }
        #else
        VarDegree vd = VarDegree( _variable, _degree );
        Coefficients::const_iterator coeffIter = mpCoefficients->find( vd );
        if( coeffIter != mpCoefficients->end() )
        {
            return coeffIter->second;
        }
        else
        {
            ex coeff = mpCoefficients->insert( pair< VarDegree, ex >( vd, mLhs.coeff( _variable, _degree ) ) ).first->second;
            return coeff;
        }
        #endif
    }

    /**
     * Determines the highest degree of all variables in this constraint.
     */
    signed Constraint::highestDegree() const
    {
        signed result = 0;
        for( symtab::const_iterator var = variables().begin(); var != variables().end(); ++var )
        {
            signed d = mLhs.degree( ex( var->second ) );
            if( d > result )
                result = d;
        }
        return result;
    }
    
    /**
     * Calculates the Cauchy bound of the left-hand side of this constraint.
     * Note, that the left-hand side must be univariate.
     * 
     * @return The Cauchy bound of the left-hand side of this constraint.
     */
    numeric Constraint::cauchyBound() const
    {
        assert( variables().size() == 1 );
        if( is_exactly_a<add>( mLhs ) )
        {
            // left-hand side is  a1*x^e1 + .. + an*x^en, 
            // where the ei are pairwise different and ai is a rational number (including 0)
            numeric cauchyBound = GiNaC::ZERO;
            numeric leadingCoefficient = GiNaC::ONE;
            // Calculate a1+ .. + an - aj,  where aj is the leading coefficient
            // and find the leading coefficient aj
            for( auto summand = mLhs.begin(); summand != mLhs.end(); ++summand )
            {
                const ex& summandEx = *summand;
                if( is_exactly_a<mul>( summandEx ) )
                {
                    const ex& factor = *--summandEx.end();
                    if( is_exactly_a<numeric>( factor ) )
                    {
                        // summand has the form  a*x^e_i  with  ai != 1
                        assert( summandEx.nops() == 2 );
                        const ex& monomial = *summandEx.begin();
                        if( is_exactly_a<symbol>(monomial) ) 
                        {
                            if( mMaxMonomeDegree == 1 ) // leading coefficient
                                leadingCoefficient = abs( ex_to<numeric>( factor ) );
                            else
                                cauchyBound += abs( ex_to<numeric>( factor ) );
                        }
                        else
                        {
                            assert( is_exactly_a<power>(monomial) );
                            assert( monomial.nops() == 2 );
                            if( *(++(monomial.end())) == mMaxMonomeDegree ) // leading coefficient
                                leadingCoefficient = abs( ex_to<numeric>( factor ) );
                            else
                                cauchyBound += abs( ex_to<numeric>( factor ) );
                        }
                    }
                    else // summand has the form:  x^e_i
                        ++cauchyBound;
                }
                else if( is_exactly_a<numeric>( summandEx ) ) // constant part, i.e. ei = 0
                    cauchyBound += abs( ex_to<numeric>( summandEx ) );
                else
                    ++cauchyBound;
            }
            cauchyBound /= leadingCoefficient;
            ++cauchyBound; // Because we skipped adding the leading coefficient before.
            return cauchyBound;
        }
        else // left-hand side is  a*x^e  ->  cauchy bound is 1
            return GiNaC::ONE;
    }

    /**
     *
     * @param The relation
     * @return
     */
    bool constraintRelationIsStrict( Constraint_Relation rel )
    {
        return (rel == CR_NEQ || rel == CR_LESS || rel == CR_GREATER);
    }

    /**
     * Gets the linear coefficients of each variable and their common constant part.
     *
     * @return The linear coefficients of each variable and their common constant part.
     */
    map<const string, numeric, strCmp> Constraint::linearAndConstantCoefficients() const
    {
        ex linearterm = mLhs.expand();
        assert( is_exactly_a<mul>( linearterm ) || is_exactly_a<symbol>( linearterm ) || is_exactly_a<numeric>( linearterm )
                || is_exactly_a<add>( linearterm ) );
        map<const string, numeric, strCmp> result = map<const string, numeric, strCmp>();
        result[""] = 0;
        if( is_exactly_a<add>( linearterm ) )
        {
            for( GiNaC::const_iterator summand = linearterm.begin(); summand != linearterm.end(); ++summand )
            {
                const ex summandEx = *summand;
                assert( is_exactly_a<mul>( summandEx ) || is_exactly_a<symbol>( summandEx ) || is_exactly_a<numeric>( summandEx ) );
                if( is_exactly_a<mul>( *summand ) )
                {
                    string symbolName   = "";
                    numeric coefficient = 1;
                    for( GiNaC::const_iterator factor = summandEx.begin(); factor != summandEx.end(); ++factor )
                    {
                        const ex factorEx = *factor;
                        assert( is_exactly_a<symbol>( factorEx ) || is_exactly_a<numeric>( factorEx ) );
                        if( is_exactly_a<symbol>( factorEx ) )
                        {
                            stringstream out;
                            out << factorEx;
                            symbolName  = out.str();
                        }
                        else if( is_exactly_a<numeric>( factorEx ) )
                        {
                            coefficient *= ex_to<numeric>( factorEx );
                        }
                    }
                    map<const string, numeric, strCmp>::iterator iter = result.find( symbolName );
                    if( iter == result.end() )
                    {
                        result.insert( pair<const string, numeric>( symbolName, coefficient ) );
                    }
                    else
                    {
                        iter->second += coefficient;
                    }
                }
                else if( is_exactly_a<symbol>( summandEx ) )
                {
                    stringstream out;
                    out << summandEx;
                    string symbolName = out.str();
                    map<const string, numeric, strCmp>::iterator iter = result.find( symbolName );
                    if( iter == result.end() )
                    {
                        result.insert( pair<const string, numeric>( symbolName, numeric( 1 ) ) );
                    }
                    else
                    {
                        iter->second += 1;
                    }
                }
                else if( is_exactly_a<numeric>( summandEx ) )
                {
                    result[""] += ex_to<numeric>( summandEx );
                }
            }
        }
        else if( is_exactly_a<mul>( linearterm ) )
        {
            string symbolName   = "";
            numeric coefficient = 1;
            for( GiNaC::const_iterator factor = linearterm.begin(); factor != linearterm.end(); ++factor )
            {
                const ex factorEx = *factor;
                assert( is_exactly_a<symbol>( factorEx ) || is_exactly_a<numeric>( factorEx ) );
                if( is_exactly_a<symbol>( factorEx ) )
                {
                    stringstream out;
                    out << factorEx;
                    symbolName = out.str();
                }
                else if( is_exactly_a<numeric>( factorEx ) )
                {
                    coefficient *= ex_to<numeric>( factorEx );
                }
            }
            map<const string, numeric, strCmp>::iterator iter = result.find( symbolName );
            if( iter == result.end() )
            {
                result.insert( pair<const string, numeric>( symbolName, coefficient ) );
            }
            else
            {
                iter->second += coefficient;
            }
        }
        else if( is_exactly_a<symbol>( linearterm ) )
        {
            stringstream out;
            out << linearterm;
            string symbolName = out.str();
            map<const string, numeric, strCmp>::iterator iter = result.find( symbolName );
            if( iter == result.end() )
            {
                result.insert( pair<const string, numeric>( symbolName, numeric( 1 ) ) );
            }
            else
            {
                iter->second += 1;
            }
        }
        else if( is_exactly_a<numeric>( linearterm ) )
        {
            result[""] += ex_to<numeric>( linearterm );
        }
        return result;
    }
    
    /**
     * 
     * @param _ex
     * @return 
     */
    bool Constraint::containsNumeric( const ex& _ex )
    {
        if( is_exactly_a<numeric>( _ex ) )
        {
            return true;
        }
        else if( is_exactly_a<add>( _ex ) || is_exactly_a<mul>( _ex ) )
        {
            return containsNumeric( _ex, _ex.end() );
        }
        else if( is_exactly_a<power>( _ex ) ) 
        {
            return containsNumeric( *_ex.begin() );
        }
        else
        {
            return false;
        }
    }
    
    /**
     * 
     * @param _ex
     * @param _exceptAt
     * @return 
     */
    bool Constraint::containsNumeric( const ex& _ex, GiNaC::const_iterator _exceptAt )
    {
        assert( is_exactly_a<add>( _ex ) || is_exactly_a<mul>( _ex ) );
        for( GiNaC::const_iterator subEx = _ex.begin(); subEx != _ex.end(); ++subEx )
        {
            if( subEx != _exceptAt )
            {
                if( containsNumeric( *subEx ) ) return true;
            }
        }
        return false;
    }

    /**
     * 
     * @param 
     * @return 
     */
    ex Constraint::normalizeA( const ex& _lhs )
    {
        numeric simplificationFactorNumer = GiNaC::ONE;
        numeric simplificationFactorDenom = GiNaC::ONE;
        if( is_exactly_a<add>( _lhs ) )
        {
            for( GiNaC::const_iterator summand = _lhs.begin(); summand != _lhs.end(); ++summand )
            {
                const ex summandEx = *summand;
                if( summand == _lhs.begin() )
                {
                    if( is_exactly_a<mul>( summandEx ) )
                    {
                        const ex factor = *--summandEx.end();
                        if( is_exactly_a<numeric>( factor ) )
                        {
                            simplificationFactorNumer = ex_to<numeric>( factor ).denom();
                            simplificationFactorDenom = ex_to<numeric>( factor ).numer();
                        }
                        assert( !containsNumeric( summandEx, --summandEx.end() ) );
                    }
                    else if( is_exactly_a<numeric>( summandEx ) )
                    {
                        simplificationFactorNumer = ex_to<numeric>( summandEx ).denom();
                        simplificationFactorDenom = ex_to<numeric>( summandEx ).numer();
                    }
                }
                else
                {
                    if( is_exactly_a<mul>( summandEx ) )
                    {
                        const ex factor = *--summandEx.end();
                        if( is_exactly_a<numeric>( factor ) )
                        {
                            simplificationFactorNumer = gcd( simplificationFactorNumer, ex_to<numeric>( factor ).denom() );
                            simplificationFactorDenom = lcm( simplificationFactorDenom, ex_to<numeric>( factor ).numer() );
                        }
                        else
                        {
                            simplificationFactorNumer = GiNaC::ONE;
                        }
                        assert( !containsNumeric( summandEx, --summandEx.end() ) );
                    }
                    else if( is_exactly_a<numeric>( summandEx ) )
                    {
                        simplificationFactorNumer = gcd( simplificationFactorNumer, ex_to<numeric>( summandEx ).denom() );
                        simplificationFactorDenom = lcm( simplificationFactorDenom, ex_to<numeric>( summandEx ).numer() );
                    }
                    else
                    {
                        simplificationFactorNumer = GiNaC::ONE;
                    }
                }
            }
        }
        else if( is_exactly_a<mul>( _lhs ) )
        {
            const ex factor = *--_lhs.end();
            if( is_exactly_a<numeric>( factor ) )
            {
                simplificationFactorNumer = ex_to<numeric>( factor ).denom();
                simplificationFactorDenom = ex_to<numeric>( factor ).numer();
            }
            assert( !containsNumeric( _lhs, --_lhs.end() ) );
        }
        return ex( _lhs * simplificationFactorNumer / simplificationFactorDenom ).expand().normal();
    }
    
    /**
     * Collects some properties of the constraint. Needs only to be applied once.
     */
    void Constraint::collectProperties()
    {
        mIsNeverPositive = true;
        mIsNeverNegative = true;
        mIsNeverZero = false;
        mMaxMonomeDegree = 1;
        mMinMonomeDegree = -1;
        mNumMonomials = 0;
        mConstantPart = 0;
        for( auto var = variables().begin(); var != variables().end(); ++var )
        {
            VarInfo varInfo = VarInfo();
            varInfo.maxDegree = 1;
            varInfo.minDegree = -1;
            varInfo.occurences = 0;
            mVarInfoMap.insert( pair< const ex, VarInfo >( var->second, varInfo ) );
        }
        if( is_exactly_a<add>( mLhs ) )
        {
            for( GiNaC::const_iterator summand = mLhs.begin(); summand != mLhs.end(); ++summand )
            {
                ++mNumMonomials;
                const ex summandEx = *summand;
                if( is_exactly_a<mul>( summandEx ) )
                {
                    unsigned monomDegree = 0;
                    for( GiNaC::const_iterator factor = summandEx.begin(); factor != summandEx.end(); ++factor )
                    {
                        const ex factorEx = *factor;
                        if( is_exactly_a<symbol>( factorEx ) )
                        {
                            mIsNeverPositive = false;
                            mIsNeverNegative = false;
                            VarInfo& varInfo = mVarInfoMap[factorEx];
                            ++varInfo.occurences;
                            varInfo.minDegree = 1;
                            ++monomDegree;
                        }
                        else if( is_exactly_a<numeric>( factorEx ) )
                        {
                            if( factorEx.info( info_flags::negative ) )
                            {
                                mIsNeverNegative = false;
                            }
                            else
                            {
                                mIsNeverPositive = false;
                            }
                        }
                        else if( is_exactly_a<power>( factorEx ) )
                        {
                            assert( factorEx.nops() == 2 );
                            ex exponent = *(++(factorEx.begin()));
                            assert( !exponent.info( info_flags::negative ) );
                            unsigned exp = static_cast<unsigned>( exponent.integer_content().to_int() );
                            if( fmod( exp, 2.0 ) != 0.0 )
                            {
                                mIsNeverPositive = false;
                                mIsNeverNegative = false;
                            }
                            ex subterm = *factorEx.begin();
                            assert( is_exactly_a<symbol>( subterm ) );
                            VarInfo& varInfo = mVarInfoMap[subterm];
                            ++varInfo.occurences;
                            if( exp > varInfo.maxDegree ) varInfo.maxDegree = exp;
                            if( exp < varInfo.minDegree ) varInfo.minDegree = exp;
                            monomDegree += exp;
                        }
                        else assert( false );
                    }
                    if( monomDegree > mMaxMonomeDegree ) mMaxMonomeDegree = monomDegree;
                    if( monomDegree < mMinMonomeDegree && monomDegree != 0 ) mMinMonomeDegree = monomDegree;
                }
                else if( is_exactly_a<symbol>( summandEx ) )
                {

                    mIsNeverPositive = false;
                    mIsNeverNegative = false;
                    VarInfo& varInfo = mVarInfoMap[summandEx];
                    ++varInfo.occurences;
                    varInfo.minDegree = 1;
                    mMinMonomeDegree = 1;
                }
                else if( is_exactly_a<numeric>( summandEx ) )
                {
                    mConstantPart += ex_to<numeric>( summandEx );
                    if( summandEx.info( info_flags::negative ) )
                    {
                        mIsNeverNegative = false;
                    }
                    else
                    {
                        mIsNeverPositive = false;
                    }
                }
                else if( is_exactly_a<power>( summandEx ) )
                {

                    assert( summandEx.nops() == 2 );
                    ex exponent = *(++(summandEx.begin()));
                    assert( !exponent.info( info_flags::negative ) );
                    unsigned exp = static_cast<unsigned>( exponent.integer_content().to_int() );
                    mIsNeverPositive = false;
                    if( fmod( exp, 2.0 ) != 0.0 )
                    {
                        mIsNeverNegative = false;
                    }
                    ex subterm = *summandEx.begin();
                    assert( is_exactly_a<symbol>( subterm ) );
                    VarInfo& varInfo = mVarInfoMap[subterm];
                    ++varInfo.occurences;
                    if( exp > varInfo.maxDegree ) varInfo.maxDegree = exp;
                    if( exp < varInfo.minDegree ) varInfo.minDegree = exp;
                    if( exp > mMaxMonomeDegree ) mMaxMonomeDegree = exp;
                    if( exp < mMinMonomeDegree ) mMinMonomeDegree = exp;
                }
                else assert( false );
            }
        }
        else if( is_exactly_a<mul>( mLhs ) )
        {
            unsigned monomDegree = 0;
            mNumMonomials = 1;
            bool hasCoefficient = false;
            for( GiNaC::const_iterator factor = mLhs.begin(); factor != mLhs.end(); ++factor )
            {
                const ex factorEx = *factor;
                if( is_exactly_a<symbol>( factorEx ) )
                {
                    mIsNeverPositive = false;
                    mIsNeverNegative = false;
                    VarInfo& varInfo = mVarInfoMap[factorEx];
                    ++varInfo.occurences;
                    varInfo.minDegree = 1;
                    ++monomDegree;
                }
                else if( is_exactly_a<numeric>( factorEx ) )
                {
                    if( factorEx.info( info_flags::negative ) )
                    {
                        mIsNeverNegative = false;
                    }
                    else
                    {
                        mIsNeverPositive = false;
                    }
                    hasCoefficient = true;
                }
                else if( is_exactly_a<power>( factorEx ) )
                {
                    assert( factorEx.nops() == 2 );
                    ex exponent = *(++factorEx.begin());
                    assert( !exponent.info( info_flags::negative ) );
                    unsigned exp = static_cast<unsigned>( exponent.integer_content().to_int() );
                    if( fmod( exp, 2.0 ) != 0.0 )
                    {
                        mIsNeverPositive = false;
                        mIsNeverNegative = false;
                    }
                    ex subterm = *factorEx.begin();
                    assert( is_exactly_a<symbol>( subterm ) );
                    VarInfo& varInfo = mVarInfoMap[subterm];
                    ++varInfo.occurences;
                    if( exp > varInfo.maxDegree ) varInfo.maxDegree = exp;
                    if( exp < varInfo.minDegree ) varInfo.minDegree = exp;
                    monomDegree += exp;
                }
                else assert( false );
            }
            if( !hasCoefficient ) mIsNeverPositive = false;
            if( monomDegree > mMaxMonomeDegree ) mMaxMonomeDegree = monomDegree;
            if( monomDegree < mMinMonomeDegree && monomDegree != 0 ) mMinMonomeDegree = monomDegree;
        }
        else if( is_exactly_a<symbol>( mLhs ) )
        {
            mNumMonomials = 1;
            mIsNeverPositive = false;
            mIsNeverNegative = false;
            VarInfo& varInfo = mVarInfoMap[mLhs];
            ++varInfo.occurences;
            varInfo.minDegree = 1;
            mMinMonomeDegree = 1;
        }
        else if( is_exactly_a<numeric>( mLhs ) )
        {
            mConstantPart += ex_to<numeric>( mLhs );
            if( mLhs.info( info_flags::negative ) )
            {
                mIsNeverNegative = false;
            }
            else
            {
                mIsNeverPositive = false;
            }
        }
        else if( is_exactly_a<power>( mLhs ) )
        {
            assert( mLhs.nops() == 2 );
            ex exponent = *(++mLhs.begin());
            assert( !exponent.info( info_flags::negative ) );
            unsigned exp = static_cast<unsigned>( exponent.integer_content().to_int() );
            mNumMonomials = 1;
            mIsNeverPositive = false;
            if( fmod( exp, 2.0 ) != 0.0 )
            {
                mIsNeverNegative = false;
            }
            ex subterm = *mLhs.begin();
            assert( is_exactly_a<symbol>( subterm ) );
            VarInfo& varInfo = mVarInfoMap[subterm];
            ++varInfo.occurences;
            if( exp > varInfo.maxDegree ) varInfo.maxDegree = exp;
            if( exp < varInfo.minDegree ) varInfo.minDegree = exp;
            if( exp > mMaxMonomeDegree ) mMaxMonomeDegree = exp;
            if( exp < mMinMonomeDegree ) mMinMonomeDegree = exp;
        }
        else assert( false );
        if( ( mConstantPart.is_negative() < 0 && mIsNeverPositive ) || ( mConstantPart.is_positive() > 0 && mIsNeverNegative ) )
        {
            mIsNeverZero = true;
        }
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
        if( (mIsNeverNegative && mRelation == CR_LEQ) || (mIsNeverPositive && mRelation == CR_GEQ) )
        {
            anythingChanged = true;
            mRelation = CR_EQ;
        }
        if( mVarInfoMap.size() == 1 && mNumMonomials == 1 && mMaxMonomeDegree > 1 )
        {
            switch( mRelation )
            {
                case CR_EQ:
                {
                    mIsNeverPositive = false;
                    mIsNeverNegative = false;
                    mLhs = mVariables.begin()->second;
                    anythingChanged = true;
                    mMaxMonomeDegree = 1;
                    mMinMonomeDegree = 1;
                    mVarInfoMap.begin()->second.maxDegree = 1;
                    mVarInfoMap.begin()->second.minDegree = 1;
                    break;
                }
                case CR_NEQ:
                {
                    mIsNeverPositive = false;
                    mIsNeverNegative = false;
                    mLhs = mVariables.begin()->second;
                    anythingChanged = true;
                    mMaxMonomeDegree = 1;
                    mMinMonomeDegree = 1;
                    mVarInfoMap.begin()->second.maxDegree = 1;
                    mVarInfoMap.begin()->second.minDegree = 1;
                    break;
                }
                case CR_LEQ:
                {
                    if( mIsNeverPositive )
                    {
                        mLhs = (-1) * mVariables.begin()->second * mVariables.begin()->second;
                        anythingChanged = true;
                        mMaxMonomeDegree = 2;
                        mMinMonomeDegree = 2;
                        mVarInfoMap.begin()->second.maxDegree = 2;
                        mVarInfoMap.begin()->second.minDegree = 2;
                    }
                    else
                    {
                        mLhs = (mLhs.coeff( mVariables.begin()->second, mMaxMonomeDegree ).info( info_flags::positive ) ? ex( 1 ) : ex( -1 ) ) * mVariables.begin()->second;
                        anythingChanged = true;
                        mMaxMonomeDegree = 1;
                        mMinMonomeDegree = 1;
                        mVarInfoMap.begin()->second.maxDegree = 1;
                        mVarInfoMap.begin()->second.minDegree = 1;
                    }
                    break;
                }
                case CR_GEQ:
                {
                    if( mIsNeverNegative )
                    {
                        mLhs = mVariables.begin()->second * mVariables.begin()->second;
                        anythingChanged = true;
                        mMaxMonomeDegree = 2;
                        mMinMonomeDegree = 2;
                        mVarInfoMap.begin()->second.maxDegree = 2;
                        mVarInfoMap.begin()->second.minDegree = 2;
                    }
                    else
                    {
                        mLhs = (mLhs.coeff( mVariables.begin()->second, mMaxMonomeDegree ).info( info_flags::positive ) ? ex( 1 ) : ex( -1 ) ) * mVariables.begin()->second;
                        anythingChanged = true;
                        mMaxMonomeDegree = 1;
                        mMinMonomeDegree = 1;
                        mVarInfoMap.begin()->second.maxDegree = 1;
                        mVarInfoMap.begin()->second.minDegree = 1;
                    }
                    break;
                }
                case CR_LESS:
                {
                    if( mIsNeverPositive )
                    {
                        mRelation = CR_NEQ;
                        mLhs = mVariables.begin()->second;
                        mIsNeverPositive = false;
                        anythingChanged = true;
                        mMaxMonomeDegree = 1;
                        mMinMonomeDegree = 1;
                        mVarInfoMap.begin()->second.maxDegree = 1;
                        mVarInfoMap.begin()->second.minDegree = 1;
                    }
                    else
                    {
                        if( mIsNeverNegative )
                        {
                            mLhs = mVariables.begin()->second * mVariables.begin()->second;
                            anythingChanged = true;
                            mMaxMonomeDegree = 2;
                            mMinMonomeDegree = 2;
                            mVarInfoMap.begin()->second.maxDegree = 2;
                            mVarInfoMap.begin()->second.minDegree = 2;
                        }
                        else
                        {
                            mLhs = (mLhs.coeff( mVariables.begin()->second, mMaxMonomeDegree ).info( info_flags::positive ) ? ex( 1 ) : ex( -1 ) ) * mVariables.begin()->second;
                            anythingChanged = true;
                            mMaxMonomeDegree = 1;
                            mMinMonomeDegree = 1;
                            mVarInfoMap.begin()->second.maxDegree = 1;
                            mVarInfoMap.begin()->second.minDegree = 1;
                        }
                    }
                    break;
                }
                case CR_GREATER:
                {
                    if( mIsNeverNegative )
                    {
                        mRelation = CR_NEQ;
                        mLhs = mVariables.begin()->second;
                        mIsNeverNegative = false;
                        anythingChanged = true;
                        mMaxMonomeDegree = 1;
                        mMinMonomeDegree = 1;
                        mVarInfoMap.begin()->second.maxDegree = 1;
                        mVarInfoMap.begin()->second.minDegree = 1;
                    }
                    else
                    {
                        if( mIsNeverPositive )
                        {
                            mLhs = (-1) * mVariables.begin()->second * mVariables.begin()->second;
                            anythingChanged = true;
                            mMaxMonomeDegree = 2;
                            mMinMonomeDegree = 2;
                            mVarInfoMap.begin()->second.maxDegree = 2;
                            mVarInfoMap.begin()->second.minDegree = 2;
                        }
                        else
                        {
                            mLhs = (mLhs.coeff( mVariables.begin()->second, mMaxMonomeDegree ).info( info_flags::positive ) ? ex( 1 ) : ex( -1 ) ) * mVariables.begin()->second;
                            anythingChanged = true;
                            mMaxMonomeDegree = 1;
                            mMinMonomeDegree = 1;
                            mVarInfoMap.begin()->second.maxDegree = 1;
                            mVarInfoMap.begin()->second.minDegree = 1;
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
        if( mVariables.size() == 1 )
        {
            ex derivate            = mLhs.diff( ex_to<symbol>( mVariables.begin()->second ), 1 );
            ex gcdOfLhsAndDerivate = gcd( mLhs, derivate );
            normalize( gcdOfLhsAndDerivate );
            ex quotient;
            if( gcdOfLhsAndDerivate != 0 && divide( mLhs, gcdOfLhsAndDerivate, quotient ) )
            {
                mMultiRootLessLhs = quotient;
            }
        }
        #ifdef SMTRAT_STRAT_Factorization
        if( mNumMonomials <= MAX_NUMBER_OF_MONOMIALS_FOR_FACTORIZATION && mVariables.size() <= MAX_DIMENSION_FOR_FACTORIZATION
            && mMaxMonomeDegree <= MAX_DEGREE_FOR_FACTORIZATION && mMaxMonomeDegree >= MIN_DEGREE_FOR_FACTORIZATION )
        {
            ex factorization = factor( mLhs );
            if( is_exactly_a<mul>( factorization ) && !is_exactly_a<mul>( mLhs ) )
            {
                mFactorization = factorization;
            }
        }
        #endif
        #ifdef SMTRAT_STRAT_PARALLEL_MODE
        for( VarInfoMap::const_iterator var = mVarInfoMap.begin(); var != mVarInfoMap.end(); ++var )
        {
            for( unsigned i = 0; i <= var->second.maxDegree; ++i )
            {
                VarDegree vd = VarDegree( var->first, i );
                mpCoefficients->insert( pair< VarDegree, ex >( vd, mLhs.coeff( var->first, i ) ) ).first->second;
            }
        }
        #endif
    }

    /**
     * Compares whether the two expressions are the same.
     *
     * @param _expressionA
     * @param _varsA
     * @param _expressionB
     * @param _varsB
     *
     * @return  -1, if the first expression is smaller than the second according to this order.
     *          0, if the first expression is equal to the second according to this order.
     *          1, if the first expression is greater than the second according to this order.
     */
    int Constraint::exCompare( const GiNaC::ex& _expressionA, const symtab& _varsA, const GiNaC::ex& _expressionB, const symtab& _varsB )
    {
        symtab::const_iterator varA = _varsA.begin();
        symtab::const_iterator varB = _varsB.begin();
        if( varA != _varsA.end() && varB != _varsB.end() )
        {
            int cmpValue = varA->first.compare( varB->first );
            if( cmpValue < 0 )
            {
                return -1;
            }
            else if( cmpValue > 0 )
            {
                return 1;
            }
            else
            {
                ex currentVar = ex( varA->second );
                signed degreeA = _expressionA.degree( currentVar );
                signed degreeB = _expressionB.degree( currentVar );
                if( degreeA < degreeB )
                {
                    return -1;
                }
                else if( degreeA > degreeB )
                {
                    return 1;
                }
                else
                {
                    varA++;
                    varB++;
                    for( int i = degreeA; i >= 0; --i )
                    {
                        symtab remVarsA = symtab( varA, _varsA.end() );
                        ex ithCoeffA    = _expressionA.coeff( currentVar, i );
                        symtab::iterator var = remVarsA.begin();
                        while( var != remVarsA.end() )
                        {
                            if( !ithCoeffA.has( ex( var->second ) ) )
                            {
                                remVarsA.erase( var++ );
                            }
                            else
                            {
                                var++;
                            }
                        }
                        symtab remVarsB = symtab( varB, _varsB.end() );
                        ex ithCoeffB    = _expressionB.coeff( currentVar, i );
                        var             = remVarsB.begin();
                        while( var != remVarsB.end() )
                        {
                            if( !ithCoeffB.has( ex( var->second ) ) )
                            {
                                remVarsB.erase( var++ );
                            }
                            else
                            {
                                var++;
                            }
                        }
                        int coeffCompResult = exCompare( ithCoeffA, remVarsA, ithCoeffB, remVarsB );
                        if( coeffCompResult < 0 )
                        {
                            return -1;
                        }
                        else if( coeffCompResult > 0 )
                        {
                            return 1;
                        }
                    }
                    return 0;
                }
            }
        }
        else if( varB != _varsB.end() )
        {
            return -1;
        }
        else if( varA != _varsA.end() )
        {
            return 1;
        }
        else
        {
            if( _expressionA < _expressionB )
            {
                return -1;
            }
            else if( _expressionA > _expressionB )
            {
                return 1;
            }
            else
            {
                return 0;
            }
        }
    }

    /**
     * Compares this constraint with the given constraint.
     *
     * @return  true,   if this constraint is LEXOGRAPHICALLY smaller than the given one;
     *          false,  otherwise.
     */
    bool Constraint::operator <( const Constraint& _constraint ) const
    {
        if( mID > 0 && _constraint.id() > 0 )
        {
            return mID < _constraint.id();
        }
        if( relation() < _constraint.relation() )
        {
            return true;
        }
        else if( relation() == _constraint.relation() )
        {
            assert( mVariables.empty() );
            if( exCompare( mLhs, variables(), _constraint.mLhs, _constraint.variables() ) == -1 )
            {
                return true;
            }
            else
            {
                return false;
            }
        }
        else
        {
            return false;
        }
    }

    /**
     * Compares this constraint with the given constraint.
     *
     * @return  true,   if this constraint is equal to the given one;
     *          false,  otherwise.
     */
    bool Constraint::operator ==( const Constraint& _constraint ) const
    {
        if( mID > 0 && _constraint.id() > 0 )
        {
            return mID == _constraint.id();
        }
        if( relation() == _constraint.relation() )
        {
            if( mLhs == _constraint.mLhs )
            {
                return true;
            }
            else
            {
                return false;
            }
        }
        else
        {
            return false;
        }
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
    string Constraint::toString( unsigned _unequalSwitch ) const
    {
        string result = "";
        ostringstream sstream;
        sstream << mLhs;
        result += sstream.str(); 
        switch( relation() )
        {
            case CR_EQ:
                result += "  = ";
                break;
            case CR_NEQ:
                if( _unequalSwitch == 1 )
                    result += " <> ";
                else if( _unequalSwitch == 2 )
                    result += " /= ";
                else // standard case
                    result += " != ";
                break;
            case CR_LESS:
                result += "  < ";
                break;
            case CR_GREATER:
                result += "  > ";
                break;
            case CR_LEQ:
                result += " <= ";
                break;
            case CR_GEQ:
                result += " >= ";
                break;
            default:
                result += "  ~ ";
        }
        result += "0";
        return result;
    }

    /**
     * Prints the constraint representation to an output stream.
     *
     * @param _out The output stream to which the constraints representation is printed.
     */
    void Constraint::print( ostream& _out ) const
    {
        _out << mLhs;
        switch( relation() )
        {
            case CR_EQ:
                _out << "=";
                break;
            case CR_NEQ:
                _out << "<>";
                break;
            case CR_LESS:
                _out << "<";
                break;
            case CR_GREATER:
                _out << ">";
                break;
            case CR_LEQ:
                _out << "<=";
                break;
            case CR_GEQ:
                _out << ">=";
                break;
            default:
                _out << "~";
        }
        _out << "0";
    }

    /**
     * Prints the constraint representation to an output stream.
     *
     * @param _out The output stream to which the constraints representation is printed.
     */
    void Constraint::print2( ostream& _out ) const
    {
        _out << mLhs;
        switch( relation() )
        {
            case CR_EQ:
                _out << "=";
                break;
            case CR_NEQ:
                _out << "!=";
                break;
            case CR_LESS:
                _out << "<";
                break;
            case CR_GREATER:
                _out << ">";
                break;
            case CR_LEQ:
                _out << "<=";
                break;
            case CR_GEQ:
                _out << ">=";
                break;
            default:
                _out << "~";
        }
        _out << "0";
    }

    /**
     * Gives the string representation of the constraint.
     *
     * @return The string representation of the constraint.
     */
    string Constraint::smtlibString( bool _resolveUnequal ) const
    {
        switch( relation() )
        {
            case CR_EQ:
            {
                return "(= " + prefixStringOf( mLhs ) + " 0)";
            }
            case CR_NEQ:
            {
                if( _resolveUnequal )
                    return "(or (< " + prefixStringOf( mLhs ) + " 0) (> " + prefixStringOf( mLhs ) + " 0))";
                else
                    "(!= " + prefixStringOf( mLhs ) + " 0)";
            }
            case CR_LESS:
            {
                return "(< " + prefixStringOf( mLhs ) + " 0)";
            }
            case CR_GREATER:
            {
                return "(> " + prefixStringOf( mLhs ) + " 0)";
            }
            case CR_LEQ:
            {
                return "(<= " + prefixStringOf( mLhs ) + " 0)";
            }
            case CR_GEQ:
            {
                return "(>= " + prefixStringOf( mLhs ) + " 0)";
            }
            default:
            {
                return "(~ " + prefixStringOf( mLhs ) + " 0)";
            }
        }
    }

    /**
     * Prints the constraint representation to an output stream.
     *
     * @param _out The output stream to which the constraints representation is printed.
     */
    void Constraint::printInPrefix( ostream& _out ) const
    {
        _out << smtlibString();
    }

    /**
     * 
     * @param _term
     * @return 
     */
    const string Constraint::prefixStringOf( const ex& _term ) const
    {
        string result = "";
        if( is_exactly_a<add>( _term ) )
        {
            result += "(+";
            for( GiNaC::const_iterator subterm = _term.begin(); subterm != _term.end(); ++subterm )
            {
                result += " " + prefixStringOf( *subterm );
            }
            result += ")";
        }
        else if( is_exactly_a<mul>( _term ) )
        {
            result += "(*";
            for( GiNaC::const_iterator subterm = _term.begin(); subterm != _term.end(); ++subterm )
            {
                result += " " + prefixStringOf( *subterm );
            }
            result += ")";
        }
        else if( is_exactly_a<power>( _term ) )
        {
            assert( _term.nops() == 2 );
            ex exponent = *(++_term.begin());
            if( exponent == 0 )
            {
                result = "1";
            }
            else
            {
                ex subterm = *_term.begin();
                int exp = exponent.integer_content().to_int();
                if( exponent.info( info_flags::negative ) )
                {
                    result += "(/ 1 ";
                    exp *= -1;
                }
                if( exp == 1 )
                {
                    result += prefixStringOf( subterm );
                }
                else
                {
                    result += "(*";
                    for( int i = 0; i < exp; ++i )
                    {
                        result += " " + prefixStringOf( subterm );
                    }
                    result += ")";
                }
                if( exponent.info( info_flags::negative ) )
                {
                    result += ")";
                }
            }
        }
        else if( is_exactly_a<numeric>( _term ) )
        {
            //TODO: negative case
            numeric num = ex_to<numeric>( _term );
            if( num.is_negative() )
            {
                result += "(- ";
            }
            if( num.is_integer() )
            {
                stringstream out;
                out << abs( num );
                result += out.str();
            }
            else
            {
                stringstream out;
                out << "(/ " << abs( num.numer() ) << " " << abs( num.denom() ) << ")";
                result += out.str();
            }
            if( num.is_negative() )
            {
                result += ")";
            }
        }
        else
        {
            stringstream out;
            out << _term;
            result += out.str();
        }
        return result;
    }
    
    /**
     * Prints the properties of this constraints on the given stream.
     *
     * @param _out The stream to print on.
     */
    void Constraint::printProperties( ostream& _out ) const
    {
        _out << "Properties:" << endl;
        _out << "   mIsNeverPositive = " << (mIsNeverPositive ? "true" : "false") << endl;
        _out << "   mIsNeverNegative = " << (mIsNeverNegative ? "true" : "false") << endl;
        _out << "   mCannotBeZero    = " << (mIsNeverZero ? "true" : "false") << endl;
        _out << "   mNumMonomials    = " << mNumMonomials << endl;
        _out << "   mMaxMonomeDegree = " << mMaxMonomeDegree << endl;
        _out << "   mMinMonomeDegree = " << mMinMonomeDegree << endl;
        _out << "   mConstantPart    = " << mConstantPart << endl;
        _out << "   Variables:" << endl;
        for( auto varInfo = mVarInfoMap.begin(); varInfo != mVarInfoMap.end(); ++varInfo )
        {
            _out << "        occurences of " << varInfo->first << " = " << varInfo->second.occurences << endl;
            _out << "        maxDegree of " << varInfo->first << "  = " << varInfo->second.maxDegree << endl;
            _out << "        minDegree of " << varInfo->first << "  = " << varInfo->second.minDegree << endl;
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
        symtab::const_iterator var1 = _constraintA->variables().begin();
        symtab::const_iterator var2 = _constraintB->variables().begin();
        while( var1 != _constraintA->variables().end() && var2 != _constraintB->variables().end() )
        {
            if( strcmp( (*var1).first.c_str(), (*var2).first.c_str() ) == 0 )
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
                case CR_EQ:
                {
                    switch( _constraintA->relation() )
                    {
                        case CR_EQ:
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
                        case CR_NEQ:
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
                        case CR_LESS:
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
                        case CR_GREATER:
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
                        case CR_LEQ:
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
                        case CR_GEQ:
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
                case CR_NEQ:
                {
                    switch( _constraintA->relation() )
                    {
                        case CR_EQ:
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
                        case CR_NEQ:
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
                        case CR_LESS:
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
                        case CR_GREATER:
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
                        case CR_LEQ:
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
                        case CR_GEQ:
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
                case CR_LESS:
                {
                    switch( _constraintA->relation() )
                    {
                        case CR_EQ:
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
                        case CR_NEQ:
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
                        case CR_LESS:
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
                        case CR_GREATER:
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
                        case CR_LEQ:
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
                        case CR_GEQ:
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
                case CR_GREATER:
                {
                    switch( _constraintA->relation() )
                    {
                        case CR_EQ:
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
                        case CR_NEQ:
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
                        case CR_LESS:
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
                        case CR_GREATER:
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
                        case CR_LEQ:
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
                        case CR_GEQ:
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
                case CR_LEQ:
                {
                    switch( _constraintA->relation() )
                    {
                        case CR_EQ:
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
                        case CR_NEQ:
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
                        case CR_LESS:
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
                        case CR_GREATER:
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
                        case CR_LEQ:
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
                        case CR_GEQ:
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
                case CR_GEQ:
                {
                    switch( _constraintA->relation() )
                    {
                        case CR_EQ:
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
                        case CR_NEQ:
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
                        case CR_LESS:
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
                        case CR_GREATER:
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
                        case CR_LEQ:
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
                        case CR_GEQ:
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
                case CR_EQ:
                {
                    switch( _constraintB->relation() )
                    {
                        case CR_EQ:
                        {
                            return NULL;
                        }
                        case CR_NEQ:
                        {
                            ex result1 = _constraintA->mLhs - _constraintB->mLhs;
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return Formula::newConstraint( 0, CR_EQ, symtab() );
                            }
                            ex result2 = _constraintA->mLhs + _constraintB->mLhs;
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( 0, CR_EQ, symtab() );
                            }
                            return NULL;
                        }
                        case CR_LESS:
                        {
                            ex result1 = _constraintA->mLhs - _constraintB->mLhs;
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return Formula::newConstraint( _constraintA->mLhs, CR_LEQ, _constraintA->variables() );
                            }
                            ex result2 = _constraintA->mLhs + _constraintB->mLhs;
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( _constraintA->mLhs, CR_GEQ, _constraintA->variables() );
                            }
                            return NULL;
                        }
                        case CR_GREATER:
                        {
                            ex result1 = _constraintA->mLhs - _constraintB->mLhs;
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return Formula::newConstraint( _constraintA->mLhs, CR_GEQ, _constraintA->variables() );
                            }
                            ex result2 = _constraintA->mLhs + _constraintB->mLhs;
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( _constraintA->mLhs, CR_LEQ, _constraintA->variables() );
                            }
                            return NULL;
                        }
                        case CR_LEQ:
                        {
                            ex result1 = _constraintA->mLhs - _constraintB->mLhs;
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return Formula::newConstraint( _constraintA->mLhs, CR_LEQ, _constraintA->variables() );
                            }
                            ex result2 = _constraintA->mLhs + _constraintB->mLhs;
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( _constraintA->mLhs, CR_GEQ, _constraintA->variables() );
                            }
                            return NULL;
                        }
                        case CR_GEQ:
                        {
                            ex result1 = _constraintA->mLhs - _constraintB->mLhs;
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return Formula::newConstraint( _constraintA->mLhs, CR_GEQ, _constraintA->variables() );
                            }
                            ex result2 = _constraintA->mLhs + _constraintB->mLhs;
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( _constraintA->mLhs, CR_LEQ, _constraintA->variables() );
                            }
                            return NULL;
                        }
                        default:
                            return NULL;
                    }
                }
                case CR_NEQ:
                {
                    switch( _constraintB->relation() )
                    {
                        case CR_EQ:
                        {
                            ex result1 = _constraintA->mLhs - _constraintB->mLhs;
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return Formula::newConstraint( 0, CR_EQ, symtab() );
                            }
                            ex result2 = _constraintA->mLhs + _constraintB->mLhs;
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( 0, CR_EQ, symtab() );
                            }
                            return NULL;
                        }
                        case CR_NEQ:
                        {
                            return NULL;
                        }
                        case CR_LESS:
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
                        case CR_GREATER:
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
                        case CR_LEQ:
                        {
                            return NULL;
                        }
                        case CR_GEQ:
                        {
                            return NULL;
                        }
                        default:
                            return NULL;
                    }
                }
                case CR_LESS:
                {
                    switch( _constraintB->relation() )
                    {
                        case CR_EQ:
                        {
                            ex result1 = _constraintA->mLhs - _constraintB->mLhs;
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return Formula::newConstraint( _constraintB->mLhs, CR_LEQ, _constraintB->variables() );
                            }
                            ex result2 = _constraintA->mLhs + _constraintB->mLhs;
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( _constraintB->mLhs, CR_GEQ, _constraintB->variables() );
                            }
                            return NULL;
                        }
                        case CR_NEQ:
                        {
                            return NULL;
                        }
                        case CR_LESS:
                        {
                            return NULL;
                        }
                        case CR_GREATER:
                        {
                            return NULL;
                        }
                        case CR_LEQ:
                        {
                            return NULL;
                        }
                        case CR_GEQ:
                        {
                            return NULL;
                        }
                        default:
                            return NULL;
                    }
                }
                case CR_GREATER:
                {
                    switch( _constraintB->relation() )
                    {
                        case CR_EQ:
                        {
                            ex result1 = _constraintA->mLhs - _constraintB->mLhs;
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return Formula::newConstraint( _constraintB->mLhs, CR_GEQ, _constraintB->variables() );
                            }
                            ex result2 = _constraintA->mLhs + _constraintB->mLhs;
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( _constraintB->mLhs, CR_LEQ, _constraintB->variables() );
                            }
                            return NULL;
                        }
                        case CR_NEQ:
                        {
                            return NULL;
                        }
                        case CR_LESS:
                        {
                            return NULL;
                        }
                        case CR_GREATER:
                        {
                            return NULL;
                        }
                        case CR_LEQ:
                        {
                            return NULL;
                        }
                        case CR_GEQ:
                        {
                            return NULL;
                        }
                        default:
                            return NULL;
                    }
                }
                case CR_LEQ:
                {
                    switch( _constraintB->relation() )
                    {
                        case CR_EQ:
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
                                return Formula::newConstraint( _constraintB->mLhs, CR_GEQ, _constraintB->variables() );
                            }
                            return NULL;
                        }
                        case CR_NEQ:
                        {
                            return NULL;
                        }
                        case CR_LESS:
                        {
                            return NULL;
                        }
                        case CR_GREATER:
                        {
                            return NULL;
                        }
                        case CR_LEQ:
                        {
                            return NULL;
                        }
                        case CR_GEQ:
                        {
                            return NULL;
                        }
                        default:
                            return NULL;
                    }
                }
                case CR_GEQ:
                {
                    switch( _constraintB->relation() )
                    {
                        case CR_EQ:
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
                                return Formula::newConstraint( _constraintB->mLhs, CR_LEQ, _constraintB->variables() );
                            }
                            return NULL;
                        }
                        case CR_NEQ:
                        {
                            return NULL;
                        }
                        case CR_LESS:
                        {
                            return NULL;
                        }
                        case CR_GREATER:
                        {
                            return NULL;
                        }
                        case CR_LEQ:
                        {
                            return NULL;
                        }
                        case CR_GEQ:
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
            case CR_EQ:
            {
                if( _constraintB->relation() == CR_NEQ )
                {
                    if( _conditionconstraint->relation() == CR_EQ )
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
            case CR_NEQ:
            {
                switch( _constraintB->relation() )
                {
                    case CR_EQ:
                    {
                        if( _conditionconstraint->relation() == CR_EQ )
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
                    case CR_LESS:
                    {
                        // Case: ( p != d or p < c ) and c > d
                        // or      ( p != d or p < c ) and c < d
                        switch( _conditionconstraint->relation() )
                        {
                            case CR_LESS:
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
                            case CR_GREATER:
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
                    case CR_GREATER:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case CR_LESS:
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
                            case CR_GREATER:
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
                    case CR_LEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case CR_LEQ:
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
                            case CR_GEQ:
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
                    case CR_GEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case CR_LEQ:
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
                            case CR_GEQ:
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
            case CR_LESS:
            {
                switch( _constraintB->relation() )
                {
                    case CR_NEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case CR_LESS:
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
                            case CR_GREATER:
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
                    case CR_LESS:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case CR_LESS:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GREATER:
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
                    case CR_GREATER:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case CR_LESS:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GREATER:
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
                    case CR_LEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
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
                    case CR_GEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
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
            case CR_GREATER:
            {
                switch( _constraintB->relation() )
                {
                    case CR_NEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case CR_LESS:
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
                            case CR_GREATER:
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
                    case CR_LESS:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case CR_LESS:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GREATER:
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
                    case CR_GREATER:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case CR_LESS:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GREATER:
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
                    case CR_LEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
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
                    case CR_GEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
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
            case CR_LEQ:
            {
                switch( _constraintB->relation() )
                {
                    case CR_NEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case CR_LEQ:
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
                            case CR_GEQ:
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
                    case CR_LESS:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
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
                    case CR_GREATER:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
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
                    case CR_LEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
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
                    case CR_GEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs - _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
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
            case CR_GEQ:
            {
                switch( _constraintB->relation() )
                {
                    case CR_NEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case CR_LEQ:
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
                            case CR_GEQ:
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
                    case CR_LESS:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
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
                    case CR_GREATER:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
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
                    case CR_LEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA->mLhs - _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
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
                    case CR_GEQ:
                    {
                        switch( _conditionconstraint->relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA->mLhs + _constraintB->mLhs + _conditionconstraint->mLhs;
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
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

