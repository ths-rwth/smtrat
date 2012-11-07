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
 * @version 2012-10-13
 */

//#define VS_DEBUG

#include "Constraint.h"
#include "ConstraintPool.h"
#include "Formula.h"

using namespace std;
using namespace GiNaC;

namespace smtrat
{
    /**
     * Constructors:
     */
    Constraint::Constraint():
        mID( 0 ),
        mIsAlwaysNegative( false ),
        mIsAlwaysPositive( false ),
        mCannotBeZero( false ),
        mNumMonomials( 0 ),
        mMaxMonomeDegree( 0 ),
        mMinMonomeDegree( 0 ),
        mRelation( CR_EQ ),
        pLhs( new ex( 0 ) ),
        mpMultiRootLessLhs( pLhs ),
        mpCoefficients( new Coefficients() ),
        mVariables(),
        mVarInfoMap()
    {
        normalize( rLhs() );
    }

    Constraint::Constraint( const GiNaC::ex& _lhs, const Constraint_Relation _cr, const symtab& _variables, unsigned _id ):
        mID( _id ),
        mIsAlwaysNegative( false ),
        mIsAlwaysPositive( false ),
        mCannotBeZero( false ),
        mNumMonomials( 0 ),
        mMaxMonomeDegree( 0 ),
        mMinMonomeDegree( 0 ),
        mRelation( _cr ),
        pLhs( new ex( _lhs ) ),
        mpMultiRootLessLhs( pLhs ),
        mpCoefficients( new Coefficients() ),
        mVariables(),
        mVarInfoMap()
    {
        normalize( rLhs() );
        if( rLhs().info( info_flags::rational ) )
        {
            mID = 0;
        }
        for( auto var = _variables.begin(); var != _variables.end(); ++var )
        {
            if( pLhs->has( var->second ) )
            {
                mVariables.insert( *var );
            }
        }
        if( mVariables.size() == 1 )
        {
            ex derivate            = lhs().diff( ex_to<symbol>( mVariables.begin()->second ), 1 );
            ex gcdOfLhsAndDerivate = gcd( lhs(), derivate );
            normalize( gcdOfLhsAndDerivate );
            ex quotient;
            if( gcdOfLhsAndDerivate != 0 && divide( lhs(), gcdOfLhsAndDerivate, quotient ) )
            {
                mpMultiRootLessLhs = new ex( quotient );
            }
        }
    }

    Constraint::Constraint( const GiNaC::ex& _lhs, const GiNaC::ex& _rhs, const Constraint_Relation& _cr, const symtab& _variables, unsigned _id ):
        mID( _id ),
        mIsAlwaysNegative( false ),
        mIsAlwaysPositive( false ),
        mCannotBeZero( false ),
        mNumMonomials( 0 ),
        mMaxMonomeDegree( 0 ),
        mMinMonomeDegree( 0 ),
        mRelation( _cr ),
        pLhs( new ex( _lhs - _rhs ) ),
        mpMultiRootLessLhs( pLhs ),
        mpCoefficients( new Coefficients() ),
        mVariables(),
        mVarInfoMap()
    {
        normalize( rLhs() );
        if( rLhs().info( info_flags::rational ) )
        {
            mID = 0;
        }
        for( auto var = _variables.begin(); var != _variables.end(); ++var )
        {
            if( pLhs->has( var->second ) )
            {
                mVariables.insert( *var );
            }
        }
        if( mVariables.size() == 1 )
        {
            ex derivate            = lhs().diff( ex_to<symbol>( mVariables.begin()->second ), 1 );
            ex gcdOfLhsAndDerivate = gcd( lhs(), derivate );
            normalize( gcdOfLhsAndDerivate );
            ex quotient;
            if( gcdOfLhsAndDerivate != 0 && divide( lhs(), gcdOfLhsAndDerivate, quotient ) )
            {
                mpMultiRootLessLhs = new ex( quotient );
            }
        }
    }

    Constraint::Constraint( const Constraint& _constraint ):
        mID( _constraint.id() ),
        mIsAlwaysNegative( _constraint.mIsAlwaysNegative ),
        mIsAlwaysPositive( _constraint.mIsAlwaysPositive ),
        mCannotBeZero( _constraint.mCannotBeZero ),
        mNumMonomials( _constraint.mNumMonomials ),
        mMaxMonomeDegree( _constraint.mMaxMonomeDegree ),
        mMinMonomeDegree( _constraint.mMinMonomeDegree ),
        mRelation( _constraint.relation() ),
        pLhs( new ex( _constraint.lhs() ) ),
        mpMultiRootLessLhs( _constraint.pMultiRootLessLhs() != _constraint.pLhs ? _constraint.mpMultiRootLessLhs : pLhs ),
        mpCoefficients( new Coefficients( *_constraint.mpCoefficients ) ),
        mVariables( _constraint.variables() ),
        mVarInfoMap( _constraint.mVarInfoMap )
    {}

    /**
     * Destructor:
     */
    Constraint::~Constraint()
    {
        if( mpMultiRootLessLhs != pLhs ) delete mpMultiRootLessLhs;
        delete pLhs;
    }

    /**
     * Methods:
     */

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

    bool evaluate( const numeric& _value, Constraint_Relation _relation )
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
                if( _value != 0 ) return true;
                else return false;
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
        if( variables().size() == 0 )
        {
            return evaluate( ex_to<numeric>( lhs() ), relation() ) ? 1 : 0;
        }
        else
        {
            switch( relation() )
            {
                case CR_EQ:
                {
                    if( mCannotBeZero ) return 0;
                    break;
                }
                case CR_NEQ:
                {
                    if( mCannotBeZero ) return 1;
                    break;
                }
                case CR_LESS:
                {
                    if( mCannotBeZero && mIsAlwaysNegative ) return 1;
                    if( mIsAlwaysPositive ) return 0;
                    break;
                }
                case CR_GREATER:
                {
                    if( mCannotBeZero && mIsAlwaysPositive ) return 1;
                    if( mIsAlwaysNegative ) return 0;
                    break;
                }
                case CR_LEQ:
                {
                    if( mIsAlwaysNegative ) return 1;
                    if( mCannotBeZero && mIsAlwaysPositive ) return 0;
                    break;
                }
                case CR_GEQ:
                {
                    if( mIsAlwaysPositive ) return 1;
                    if( mCannotBeZero && mIsAlwaysNegative ) return 0;
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
     * @param _assignment
     * @return
     */
    unsigned Constraint::satisfiedBy( exmap& _assignment ) const
    {
        ex tmp = lhs().subs( _assignment );
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
     *
     * @param _variable
     * @param _degree
     * @return
     */
    const ex& Constraint::coefficient( const ex& _variable, int _degree ) const
    {
        VarDegree vd = VarDegree( _variable, _degree );
        Coefficients::const_iterator coeffIter = mpCoefficients->find( vd );
        if( coeffIter != mpCoefficients->end() )
        {
            return coeffIter->second;
        }
        else
        {
            return mpCoefficients->insert( pair< VarDegree, ex >( vd, lhs().coeff( _variable, _degree ) ) ).first->second;
        }
    }

    /**
     *
     * @param _variable
     * @return
     */
    unsigned Constraint::maxDegree( const ex& _variable ) const
    {
        VarInfoMap::const_iterator varInfo = mVarInfoMap.find( _variable );
        if( varInfo != mVarInfoMap.end() )
        {
            return varInfo->second.maxDegree;
        }
        else
        {
            return 0;
        }
    }

    /**
     *
     * @param _variable
     * @return
     */
    unsigned Constraint::minDegree( const ex& _variable ) const
    {
        VarInfoMap::const_iterator varInfo = mVarInfoMap.find( _variable );
        if( varInfo != mVarInfoMap.end() )
        {
            return varInfo->second.minDegree;
        }
        else
        {
            return 0;
        }
    }

    /**
     *
     * @param _variable
     * @return
     */
    unsigned Constraint::occurences( const ex& _variable ) const
    {
        VarInfoMap::const_iterator varInfo = mVarInfoMap.find( _variable );
        if( varInfo != mVarInfoMap.end() )
        {
            return varInfo->second.occurences;
        }
        else
        {
            return 0;
        }
    }

    /**
     *
     * @param _variable
     * @return
     */
    const VarInfo& Constraint::varInfo( const ex& _variable ) const
    {
        VarInfoMap::const_iterator varInfo = mVarInfoMap.find( _variable );
        assert( varInfo != mVarInfoMap.end() );
        return varInfo->second;
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
     * Determines the highest degree of all variables in this constraint.
     */
    signed Constraint::highestDegree() const
    {
        signed result = 0;
        for( symtab::const_iterator var = variables().begin(); var != variables().end(); ++var )
        {
            signed d = lhs().degree( ex( var->second ) );
            if( d > result )
                result = d;
        }
        return result;
    }

    /**
     *
     * @return
     */
    unsigned Constraint::maxDegree() const
    {
        return mMaxMonomeDegree;
    }

    /**
     * Checks whether the constraint is linear in all variables.
     */
    bool Constraint::isLinear() const
    {
        return mMaxMonomeDegree < 2;
    }

    /**
     * Gets the linear coefficients of each variable and their common constant part.
     *
     * @return The linear coefficients of each variable and their common constant part.
     */
    map<const string, numeric, strCmp> Constraint::linearAndConstantCoefficients() const
    {
        ex linearterm = lhs().expand();
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
     */
    void Constraint::collectProperties()
    {
//        cout << endl << "initialize " << lhs() << endl;
        mIsAlwaysNegative = true;
        mIsAlwaysPositive = true;
        mCannotBeZero = false;
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
        if( is_exactly_a<add>( lhs() ) )
        {
            for( GiNaC::const_iterator summand = lhs().begin(); summand != lhs().end(); ++summand )
            {
                const ex summandEx = *summand;
                if( is_exactly_a<mul>( summandEx ) )
                {
                    unsigned monomDegree = 0;
                    ++mNumMonomials;
                    for( GiNaC::const_iterator factor = summandEx.begin(); factor != summandEx.end(); ++factor )
                    {
                        const ex factorEx = *factor;
                        if( is_exactly_a<symbol>( factorEx ) )
                        {
                            mIsAlwaysNegative = false;
                            mIsAlwaysPositive = false;
                            VarInfo& varInfo = mVarInfoMap[factorEx];
                            ++varInfo.occurences;
                            varInfo.minDegree = 1;
                            ++monomDegree;
                        }
                        else if( is_exactly_a<numeric>( factorEx ) )
                        {
                            if( factorEx.info( info_flags::negative ) )
                            {
                                mIsAlwaysPositive = false;
                            }
                            else
                            {
                                mIsAlwaysNegative = false;
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
                                mIsAlwaysNegative = false;
                                mIsAlwaysPositive = false;
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
                    ++mNumMonomials;
                    mIsAlwaysNegative = false;
                    mIsAlwaysPositive = false;
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
                        mIsAlwaysPositive = false;
                    }
                    else
                    {
                        mIsAlwaysNegative = false;
                    }
                }
                else if( is_exactly_a<power>( summandEx ) )
                {
                    ++mNumMonomials;
                    assert( summandEx.nops() == 2 );
                    ex exponent = *(++(summandEx.begin()));
                    assert( !exponent.info( info_flags::negative ) );
                    unsigned exp = static_cast<unsigned>( exponent.integer_content().to_int() );
                    mIsAlwaysNegative = false;
                    if( fmod( exp, 2.0 ) != 0.0 )
                    {
                        mIsAlwaysPositive = false;
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
        else if( is_exactly_a<mul>( lhs() ) )
        {
            unsigned monomDegree = 0;
            for( GiNaC::const_iterator factor = lhs().begin(); factor != lhs().end(); ++factor )
            {
                const ex factorEx = *factor;
                if( is_exactly_a<symbol>( factorEx ) )
                {
                    mIsAlwaysNegative = false;
                    mIsAlwaysPositive = false;
                    mNumMonomials = 1;
                    VarInfo& varInfo = mVarInfoMap[factorEx];
                    ++varInfo.occurences;
                    varInfo.minDegree = 1;
                    ++monomDegree;
                }
                else if( is_exactly_a<numeric>( factorEx ) )
                {
                    if( factorEx.info( info_flags::negative ) )
                    {
                        mIsAlwaysPositive = false;
                    }
                    else
                    {
                        mIsAlwaysNegative = false;
                    }
                }
                else if( is_exactly_a<power>( factorEx ) )
                {
                    mNumMonomials = 1;
                    assert( factorEx.nops() == 2 );
                    ex exponent = *(++factorEx.begin());
                    assert( !exponent.info( info_flags::negative ) );
                    unsigned exp = static_cast<unsigned>( exponent.integer_content().to_int() );
                    if( fmod( exp, 2.0 ) != 0.0 )
                    {
                        mIsAlwaysNegative = false;
                        mIsAlwaysPositive = false;
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
        else if( is_exactly_a<symbol>( lhs() ) )
        {
            mNumMonomials = 1;
            mIsAlwaysNegative = false;
            mIsAlwaysPositive = false;
            VarInfo& varInfo = mVarInfoMap[lhs()];
            ++varInfo.occurences;
            varInfo.minDegree = 1;
            mMinMonomeDegree = 1;
        }
        else if( is_exactly_a<numeric>( lhs() ) )
        {
            mConstantPart += ex_to<numeric>( lhs() );
            if( lhs().info( info_flags::negative ) )
            {
                mIsAlwaysPositive = false;
            }
            else
            {
                mIsAlwaysNegative = false;
            }
        }
        else if( is_exactly_a<power>( lhs() ) )
        {
            assert( lhs().nops() == 2 );
            ex exponent = *(++lhs().begin());
            assert( !exponent.info( info_flags::negative ) );
            unsigned exp = static_cast<unsigned>( exponent.integer_content().to_int() );
            mNumMonomials = 1;
            mIsAlwaysNegative = false;
            if( fmod( exp, 2.0 ) != 0.0 )
            {
                mIsAlwaysPositive = false;
            }
            ex subterm = *lhs().begin();
            assert( is_exactly_a<symbol>( subterm ) );
            VarInfo& varInfo = mVarInfoMap[subterm];
            ++varInfo.occurences;
            if( exp > varInfo.maxDegree ) varInfo.maxDegree = exp;
            if( exp < varInfo.minDegree ) varInfo.minDegree = exp;
            if( exp > mMaxMonomeDegree ) mMaxMonomeDegree = exp;
            if( exp < mMinMonomeDegree ) mMinMonomeDegree = exp;
        }
        else assert( false );
        if( ( mConstantPart.is_negative() < 0 && mIsAlwaysNegative ) || ( mConstantPart.is_positive() > 0 && mIsAlwaysPositive ) )
        {
            mCannotBeZero = true;
        }

//        cout << "mIsAlwaysNegative: " << mIsAlwaysNegative << endl;
//        cout << "mIsAlwaysPositive: " << mIsAlwaysPositive << endl;
//        cout << "mCannotBeZero    : " << mCannotBeZero << endl;
//        cout << "mNumMonomials    : " << mNumMonomials << endl;
//        cout << "mMaxMonomeDegree : " << mMaxMonomeDegree << endl;
//        cout << "mMinMonomeDegree : " << mMinMonomeDegree << endl;
//        cout << "mConstantPart    : " << mConstantPart << endl;
//        cout << "Variables:" << endl;
//        for( auto var = variables().begin(); var != variables().end(); ++var )
//        {
//            VarInfo& varInfo = mVarInfoMap[var->second];
//            cout << "     occurences of " << var->first << " : " << varInfo.occurences << endl;
//            cout << "     maxDegree of " << var->first << "  : " << varInfo.maxDegree << endl;
//            cout << "     minDegree of " << var->first << "  : " << varInfo.minDegree << endl;
//        }
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
            if( exCompare( lhs(), variables(), _constraint.lhs(), _constraint.variables() ) == -1 )
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
            if( lhs() == _constraint.lhs() )
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
     *
     * @param _ostream
     * @param _constraint
     * @return
     */
    ostream& operator <<( ostream& _ostream, const Constraint& _constraint )
    {
        _ostream << _constraint.toString();
        return _ostream;
    }

    /**
     * Simplifies this constraint.
     */
    void Constraint::simplify()
    {
        if( !variables().empty() )
        {
            ex un, con, prim;
            lhs().unitcontprim( ex( variables().begin()->second ), un, con, prim );
            if( con.info( info_flags::rational ) )
            {
                if( relation() == CR_EQ || relation() == CR_NEQ )
                {
                    rLhs() = prim;
                }
                else
                {
                    rLhs() = prim * un;
                }
            }
        }
    }

    void Constraint::getVariables( const ex& _term, symtab& _variables )
    {
        if( _term.nops() > 1 )
        {
            for( GiNaC::const_iterator subterm = _term.begin(); subterm != _term.end(); ++subterm )
            {
                getVariables( *subterm, _variables );
            }
        }
        else if( is_exactly_a<symbol>( _term ) )
        {
            stringstream out;
            out << _term;
            _variables.insert( pair< string, symbol >( out.str(), ex_to<symbol>( _term ) ) );
        }
    }

    /**
     * Gives the string representation of the constraint.
     *
     * @return The string representation of the constraint.
     */
    string Constraint::toString() const
    {
        string result = "";
        ostringstream sstream;
        sstream << lhs();
        result += sstream.str();
        switch( relation() )
        {
            case CR_EQ:
                result += "  = ";
                break;
            case CR_NEQ:
                result += " <> ";
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
        _out << lhs();
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
        _out << lhs();
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
    string Constraint::smtlibString() const
    {
        switch( relation() )
        {
            case CR_EQ:
            {
                return "(= " + prefixStringOf( lhs() ) + " 0)";
            }
            case CR_NEQ:
            {
                return "(or (< " + prefixStringOf( lhs() ) + " 0) (> " + prefixStringOf( lhs() ) + " 0))";
            }
            case CR_LESS:
            {
                return "(< " + prefixStringOf( lhs() ) + " 0)";
            }
            case CR_GREATER:
            {
                return "(> " + prefixStringOf( lhs() ) + " 0)";
            }
            case CR_LEQ:
            {
                return "(<= " + prefixStringOf( lhs() ) + " 0)";
            }
            case CR_GEQ:
            {
                return "(>= " + prefixStringOf( lhs() ) + " 0)";
            }
            default:
            {
                return "(~ " + prefixStringOf( lhs() ) + " 0)";
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
    signed Constraint::compare( const Constraint& _constraintA, const Constraint& _constraintB )
    {
        if( _constraintA.variables().empty() || _constraintB.variables().empty() ) return 0;
        symtab::const_iterator var1 = _constraintA.variables().begin();
        symtab::const_iterator var2 = _constraintB.variables().begin();
        while( var1 != _constraintA.variables().end() && var2 != _constraintB.variables().end() )
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
        if( var1 == _constraintA.variables().end() && var2 == _constraintB.variables().end() )
        {
            ex lcoeffA = _constraintA.lhs().lcoeff( ex( _constraintA.variables().begin()->second ) );
            ex lcoeffB = _constraintB.lhs().lcoeff( ex( _constraintB.variables().begin()->second ) );
            ex lhsA    = _constraintA.lhs();
            ex lhsB    = _constraintB.lhs();
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
            switch( _constraintB.relation() )
            {
                case CR_EQ:
                {
                    switch( _constraintA.relation() )
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
                    switch( _constraintA.relation() )
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
                    switch( _constraintA.relation() )
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
                    switch( _constraintA.relation() )
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
                    switch( _constraintA.relation() )
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
                    switch( _constraintA.relation() )
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
                            ex result1 = _constraintA->lhs() - _constraintB->lhs();
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return Formula::newConstraint( 0, CR_EQ );
                            }
                            ex result2 = _constraintA->lhs() + _constraintB->lhs();
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( 0, CR_EQ );
                            }
                            return NULL;
                        }
                        case CR_LESS:
                        {
                            ex result1 = _constraintA->lhs() - _constraintB->lhs();
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return Formula::newConstraint( _constraintA->lhs(), CR_LEQ, _constraintA->variables() );
                            }
                            ex result2 = _constraintA->lhs() + _constraintB->lhs();
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( _constraintA->lhs(), CR_GEQ, _constraintA->variables() );
                            }
                            return NULL;
                        }
                        case CR_GREATER:
                        {
                            ex result1 = _constraintA->lhs() - _constraintB->lhs();
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return Formula::newConstraint( _constraintA->lhs(), CR_GEQ, _constraintA->variables() );
                            }
                            ex result2 = _constraintA->lhs() + _constraintB->lhs();
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( _constraintA->lhs(), CR_LEQ, _constraintA->variables() );
                            }
                            return NULL;
                        }
                        case CR_LEQ:
                        {
                            ex result1 = _constraintA->lhs() - _constraintB->lhs();
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return Formula::newConstraint( _constraintA->lhs(), CR_LEQ, _constraintA->variables() );
                            }
                            ex result2 = _constraintA->lhs() + _constraintB->lhs();
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( _constraintA->lhs(), CR_GEQ, _constraintA->variables() );
                            }
                            return NULL;
                        }
                        case CR_GEQ:
                        {
                            ex result1 = _constraintA->lhs() - _constraintB->lhs();
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return Formula::newConstraint( _constraintA->lhs(), CR_GEQ, _constraintA->variables() );
                            }
                            ex result2 = _constraintA->lhs() + _constraintB->lhs();
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( _constraintA->lhs(), CR_LEQ, _constraintA->variables() );
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
                            ex result1 = _constraintA->lhs() - _constraintB->lhs();
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return Formula::newConstraint( 0, CR_EQ, symtab() );
                            }
                            ex result2 = _constraintA->lhs() + _constraintB->lhs();
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
                            ex result1 = _constraintA->lhs() - _constraintB->lhs();
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return _constraintA;
                            }
                            ex result2 = _constraintA->lhs() + _constraintB->lhs();
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return _constraintA;
                            }
                            return NULL;
                        }
                        case CR_GREATER:
                        {
                            ex result1 = _constraintA->lhs() - _constraintB->lhs();
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return _constraintA;
                            }
                            ex result2 = _constraintA->lhs() + _constraintB->lhs();
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
                            ex result1 = _constraintA->lhs() - _constraintB->lhs();
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return Formula::newConstraint( _constraintB->lhs(), CR_LEQ, _constraintB->variables() );
                            }
                            ex result2 = _constraintA->lhs() + _constraintB->lhs();
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( _constraintB->lhs(), CR_GEQ, _constraintB->variables() );
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
                            ex result1 = _constraintA->lhs() - _constraintB->lhs();
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return Formula::newConstraint( _constraintB->lhs(), CR_GEQ, _constraintB->variables() );
                            }
                            ex result2 = _constraintA->lhs() + _constraintB->lhs();
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( _constraintB->lhs(), CR_LEQ, _constraintB->variables() );
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
                            ex result1 = _constraintA->lhs() - _constraintB->lhs();
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return _constraintA;
                            }
                            ex result2 = _constraintA->lhs() + _constraintB->lhs();
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( _constraintB->lhs(), CR_GEQ, _constraintB->variables() );
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
                            ex result1 = _constraintA->lhs() - _constraintB->lhs();
                            normalize( result1 );
                            if( result1 == 0 )
                            {
                                return _constraintA;
                            }
                            ex result2 = _constraintA->lhs() + _constraintB->lhs();
                            normalize( result2 );
                            if( result2 == 0 )
                            {
                                return Formula::newConstraint( _constraintB->lhs(), CR_LEQ, _constraintB->variables() );
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
    bool Constraint::combineConstraints( const Constraint& _constraintA, const Constraint& _constraintB, const Constraint& _conditionconstraint )
    {
        symtab::const_iterator var1 = _constraintA.variables().begin();
        symtab::const_iterator var2 = _constraintB.variables().begin();
        symtab::const_iterator var3 = _conditionconstraint.variables().begin();
        // Checks if the three constraints are paarwise different from each other
        while( var1 != _constraintA.variables().end() && var2 != _constraintB.variables().end() )
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
        var1 = _constraintA.variables().begin();
        var2 = _constraintB.variables().begin();
        while( var1 != _constraintA.variables().end() && var3 != _conditionconstraint.variables().end() )
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
        var1 = _constraintA.variables().begin();
        var3 = _conditionconstraint.variables().begin();
        while( var2 != _constraintB.variables().end() && var3 != _conditionconstraint.variables().end() )
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
        switch( _constraintA.relation() )
        {
            case CR_EQ:
            {
                if( _constraintB.relation() == CR_NEQ )
                {
                    if( _conditionconstraint.relation() == CR_EQ )
                    {
                        // Case: ( p = c or p != d ) and c = d
                        ex result = _constraintA.lhs() - _constraintB.lhs() + _conditionconstraint.lhs();
                        normalize( result );
                        if( result == 0 )
                            return true;
                        result = _constraintA.lhs() - _constraintB.lhs() - _conditionconstraint.lhs();
                        normalize( result );
                        if( result == 0 )
                            return true;
                        result = _constraintA.lhs() + _constraintB.lhs() + _conditionconstraint.lhs();
                        normalize( result );
                        if( result == 0 )
                            return true;
                        result = _constraintA.lhs() + _constraintB.lhs() - _conditionconstraint.lhs();
                        normalize( result );
                        if( result == 0 )
                            return true;
                    }
                }
                return false;
            }
            case CR_NEQ:
            {
                switch( _constraintB.relation() )
                {
                    case CR_EQ:
                    {
                        if( _conditionconstraint.relation() == CR_EQ )
                        {
                            // Case: ( p != c or p = d ) and c = d
                            ex result = _constraintA.lhs() - _constraintB.lhs() + _conditionconstraint.lhs();
                            normalize( result );
                            if( result == 0 )
                                return true;
                            result = _constraintA.lhs() - _constraintB.lhs() - _conditionconstraint.lhs();
                            normalize( result );
                            if( result == 0 )
                                return true;
                            result = _constraintA.lhs() + _constraintB.lhs() + _conditionconstraint.lhs();
                            normalize( result );
                            if( result == 0 )
                                return true;
                            result = _constraintA.lhs() + _constraintB.lhs() - _conditionconstraint.lhs();
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
                        switch( _conditionconstraint.relation() )
                        {
                            case CR_LESS:
                            {
                                ex result = _constraintA.lhs() - _constraintB.lhs() + _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA.lhs() + _constraintB.lhs() - _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GREATER:
                            {
                                ex result = _constraintA.lhs() + _constraintB.lhs() + _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA.lhs() - _constraintB.lhs() - _conditionconstraint.lhs();
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
                        switch( _conditionconstraint.relation() )
                        {
                            case CR_LESS:
                            {
                                ex result = _constraintA.lhs() - _constraintB.lhs() - _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA.lhs() + _constraintB.lhs() + _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GREATER:
                            {
                                ex result = _constraintA.lhs() + _constraintB.lhs() - _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA.lhs() - _constraintB.lhs() + _conditionconstraint.lhs();
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
                        switch( _conditionconstraint.relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA.lhs() - _constraintB.lhs() + _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA.lhs() + _constraintB.lhs() - _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
                            {
                                ex result = _constraintA.lhs() + _constraintB.lhs() + _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA.lhs() - _constraintB.lhs() - _conditionconstraint.lhs();
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
                        switch( _conditionconstraint.relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA.lhs() + _constraintB.lhs() + _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA.lhs() - _constraintB.lhs() - _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
                            {
                                ex result = _constraintA.lhs() - _constraintB.lhs() + _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA.lhs() + _constraintB.lhs() - _conditionconstraint.lhs();
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
                switch( _constraintB.relation() )
                {
                    case CR_NEQ:
                    {
                        switch( _conditionconstraint.relation() )
                        {
                            case CR_LESS:
                            {
                                ex result = _constraintA.lhs() - _constraintB.lhs() - _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA.lhs() + _constraintB.lhs() - _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GREATER:
                            {
                                ex result = _constraintA.lhs() + _constraintB.lhs() + _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA.lhs() - _constraintB.lhs() + _conditionconstraint.lhs();
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
                        switch( _conditionconstraint.relation() )
                        {
                            case CR_LESS:
                            {
                                ex result = _constraintA.lhs() + _constraintB.lhs() - _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GREATER:
                            {
                                ex result = _constraintA.lhs() + _constraintB.lhs() + _conditionconstraint.lhs();
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
                        switch( _conditionconstraint.relation() )
                        {
                            case CR_LESS:
                            {
                                ex result = _constraintA.lhs() - _constraintB.lhs() - _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GREATER:
                            {
                                ex result = _constraintA.lhs() - _constraintB.lhs() + _conditionconstraint.lhs();
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
                        switch( _conditionconstraint.relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA.lhs() + _constraintB.lhs() - _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
                            {
                                ex result = _constraintA.lhs() + _constraintB.lhs() + _conditionconstraint.lhs();
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
                        switch( _conditionconstraint.relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA.lhs() - _constraintB.lhs() - _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
                            {
                                ex result = _constraintA.lhs() - _constraintB.lhs() + _conditionconstraint.lhs();
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
                switch( _constraintB.relation() )
                {
                    case CR_NEQ:
                    {
                        switch( _conditionconstraint.relation() )
                        {
                            case CR_LESS:
                            {
                                ex result = _constraintA.lhs() - _constraintB.lhs() + _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA.lhs() + _constraintB.lhs() + _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GREATER:
                            {
                                ex result = _constraintA.lhs() + _constraintB.lhs() - _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA.lhs() - _constraintB.lhs() - _conditionconstraint.lhs();
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
                        switch( _conditionconstraint.relation() )
                        {
                            case CR_LESS:
                            {
                                ex result = _constraintA.lhs() - _constraintB.lhs() + _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GREATER:
                            {
                                ex result = _constraintA.lhs() - _constraintB.lhs() - _conditionconstraint.lhs();
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
                        switch( _conditionconstraint.relation() )
                        {
                            case CR_LESS:
                            {
                                ex result = _constraintA.lhs() + _constraintB.lhs() + _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GREATER:
                            {
                                ex result = _constraintA.lhs() + _constraintB.lhs() - _conditionconstraint.lhs();
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
                        switch( _conditionconstraint.relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA.lhs() - _constraintB.lhs() + _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
                            {
                                ex result = _constraintA.lhs() - _constraintB.lhs() + _conditionconstraint.lhs();
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
                        switch( _conditionconstraint.relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA.lhs() + _constraintB.lhs() + _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
                            {
                                ex result = _constraintA.lhs() + _constraintB.lhs() - _conditionconstraint.lhs();
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
                switch( _constraintB.relation() )
                {
                    case CR_NEQ:
                    {
                        switch( _conditionconstraint.relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA.lhs() - _constraintB.lhs() - _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA.lhs() + _constraintB.lhs() - _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
                            {
                                ex result = _constraintA.lhs() + _constraintB.lhs() + _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA.lhs() - _constraintB.lhs() + _conditionconstraint.lhs();
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
                        switch( _conditionconstraint.relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA.lhs() + _constraintB.lhs() - _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
                            {
                                ex result = _constraintA.lhs() + _constraintB.lhs() + _conditionconstraint.lhs();
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
                        switch( _conditionconstraint.relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA.lhs() - _constraintB.lhs() - _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
                            {
                                ex result = _constraintA.lhs() - _constraintB.lhs() + _conditionconstraint.lhs();
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
                        switch( _conditionconstraint.relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA.lhs() + _constraintB.lhs() - _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
                            {
                                ex result = _constraintA.lhs() + _constraintB.lhs() + _conditionconstraint.lhs();
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
                        switch( _conditionconstraint.relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA.lhs() - _constraintB.lhs() - _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
                            {
                                ex result = _constraintA.lhs() - _constraintB.lhs() + _conditionconstraint.lhs();
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
                switch( _constraintB.relation() )
                {
                    case CR_NEQ:
                    {
                        switch( _conditionconstraint.relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA.lhs() + _constraintB.lhs() + _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA.lhs() - _constraintB.lhs() + _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
                            {
                                ex result = _constraintA.lhs() - _constraintB.lhs() - _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                result = _constraintA.lhs() + _constraintB.lhs() - _conditionconstraint.lhs();
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
                        switch( _conditionconstraint.relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA.lhs() - _constraintB.lhs() + _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
                            {
                                ex result = _constraintA.lhs() - _constraintB.lhs() - _conditionconstraint.lhs();
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
                        switch( _conditionconstraint.relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA.lhs() + _constraintB.lhs() + _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
                            {
                                ex result = _constraintA.lhs() + _constraintB.lhs() - _conditionconstraint.lhs();
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
                        switch( _conditionconstraint.relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA.lhs() - _constraintB.lhs() + _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
                            {
                                ex result = _constraintA.lhs() - _constraintB.lhs() - _conditionconstraint.lhs();
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
                        switch( _conditionconstraint.relation() )
                        {
                            case CR_LEQ:
                            {
                                ex result = _constraintA.lhs() + _constraintB.lhs() + _conditionconstraint.lhs();
                                normalize( result );
                                if( result == 0 )
                                    return true;
                                return false;
                            }
                            case CR_GEQ:
                            {
                                ex result = _constraintA.lhs() + _constraintB.lhs() - _conditionconstraint.lhs();
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

