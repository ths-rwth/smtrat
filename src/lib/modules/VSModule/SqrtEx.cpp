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
 * Class to create a square root expression object.
 * @author Florian Corzilius
 * @since 2011-05-26
 * @version 2011-12-05
 */

#include "SqrtEx.h"

namespace vs
{
    using namespace std;
    using namespace GiNaC;

    /**
     * Constructors:
     */
    SqrtEx::SqrtEx()
    {
        mpConstantPart = new ex( 0 );
        mpFactor       = new ex( 0 );
        mpDenominator  = new ex( 1 );
        mpRadicand     = new ex( 0 );
        mVariables = symtab();
    }

    SqrtEx::SqrtEx( const GiNaC::ex& _ex, const symtab& _variables )
    {
        mpConstantPart = new ex( _ex.numer() );
        mpFactor       = new ex( 0 );
        mpDenominator  = new ex( _ex.denom() );
        mpRadicand     = new ex( 0 );
        mVariables = symtab();
        for( auto var = _variables.begin(); var != _variables.end(); ++var )
        {
            if( _ex.has( var->second ) )
            {
                mVariables.insert( *var );
            }
        }
    }

    SqrtEx::SqrtEx( const GiNaC::ex& _constantPart, const GiNaC::ex& _factor, const GiNaC::ex& _denominator, const GiNaC::ex& _radicand, const symtab& _variables )
    {
        assert( _denominator != 0 );
        assert( !_radicand.info( info_flags::rational ) || _radicand.info( info_flags::nonnegative ) );
        mpConstantPart = new ex( _constantPart );
        if( _radicand == 0 )
        {
            mpFactor = new ex( 0 );
        }
        else
        {
            mpFactor = new ex( _factor );
        }
        if( _factor == 0 )
        {
            mpRadicand = new ex( 0 );
        }
        else
        {
            mpRadicand = new ex( _radicand );
        }
        if( *mpFactor == 0 && *mpConstantPart == 0 )
        {
            mpDenominator = new ex( 1 );
        }
        else
        {
            mpDenominator = new ex( _denominator );
        }
        mVariables = symtab();
        for( auto var = _variables.begin(); var != _variables.end(); ++var )
        {
            if( _constantPart.has( var->second ) )
            {
                mVariables.insert( *var );
            }
        }
        for( auto var = _variables.begin(); var != _variables.end(); ++var )
        {
            if( _factor.has( var->second ) )
            {
                mVariables.insert( *var );
            }
        }
        for( auto var = _variables.begin(); var != _variables.end(); ++var )
        {
            if( _denominator.has( var->second ) )
            {
                mVariables.insert( *var );
            }
        }
        for( auto var = _variables.begin(); var != _variables.end(); ++var )
        {
            if( _radicand.has( var->second ) )
            {
                mVariables.insert( *var );
            }
        }
    }

    SqrtEx::SqrtEx( const SqrtEx& _sqrtEx )
    {
        mpConstantPart = new ex( _sqrtEx.constantPart() );
        mpFactor       = new ex( _sqrtEx.factor() );
        mpDenominator  = new ex( _sqrtEx.denominator() );
        mpRadicand     = new ex( _sqrtEx.radicand() );
        mVariables     = symtab( _sqrtEx.variables() );
    }

    /**
     * Destructor:
     */
    SqrtEx::~SqrtEx()
    {
        delete mpConstantPart;
        delete mpFactor;
        delete mpDenominator;
        delete mpRadicand;
    }

    /**
     * Methods:
     */

    /**
     * Determines, whether the given variable occurs in this square root expression.
     *
     * @param _variable     The variable to search for.
     *
     * @return  true,   if the variable occurs in this square root expression;
     *          false,  otherwise.
     */
    bool SqrtEx::hasVariable( const string& _variable ) const
    {
        return mVariables.find( _variable ) != mVariables.end();
    }

    /**
     * Gives the expression corresponding to the square root expression.
     *
     * @return Expression, which corresponds to the square root expression.
     */
    ex SqrtEx::expression() const
    {
        if( hasSqrt() )
        {
            return (constantPart() + factor() * sqrt( radicand() )) / denominator();
        }
        else
        {
            return constantPart() / denominator();
        }
    }

    /**
     * @param _sqrtEx   Square root expression to compare with.
     *
     * @return  true,   if this square root expression and the given one are equal;
     *          false,  otherwise.
     */
    bool SqrtEx::operator ==( const SqrtEx& _sqrtEx ) const
    {
        ex difference = expression() - _sqrtEx.expression();
        normalize( difference );
        if( difference == 0 )
        {
            return true;
        }
        else
        {
            return false;
        }
    }

    /**
     * @param _sqrtEx   Square root expression to compare with.
     *
     * @return  true,   if this square root expression and the given one are equal;
     *          false,  otherwise.
     */
    SqrtEx& SqrtEx::operator = ( const SqrtEx& _sqrtEx )
    {
        if( this != &_sqrtEx )
        {
            mpConstantPart = new ex( _sqrtEx.constantPart() );
            mpFactor       = new ex( _sqrtEx.factor() );
            mpDenominator  = new ex( _sqrtEx.denominator() );
            if( factor() == 0 )
            {
                mpRadicand = new ex( 0 );
            }
            else
            {
                mpRadicand = new ex( _sqrtEx.radicand() );
            }
        }
        return *this;
    }

    /**
     * @param _sqrtEx   Square root expression to compare with.
     *
     * @return  true,   if this square root expression and the given one are equal;
     *          false,  otherwise.
     */
    SqrtEx& SqrtEx::operator = ( const ex& _ex )
    {
        mpConstantPart = new ex( _ex.numer() );
        mpFactor       = new ex( 0 );
        mpDenominator  = new ex( _ex.denom() );
        mpRadicand     = new ex( 0 );
        return *this;
    }

    /**
     * @param _sqrtEx1  First summand.
     * @param _sqrtEx2  Second summand.
     *
     * @return Sum.
     */
    SqrtEx operator +( const SqrtEx& _sqrtEx1, const SqrtEx& _sqrtEx2 )
    {
        assert( !_sqrtEx1.hasSqrt() ||!_sqrtEx2.hasSqrt() || _sqrtEx1.radicand() == _sqrtEx2.radicand() );
        symtab vars = symtab( _sqrtEx1.variables() );
        vars.insert( _sqrtEx2.variables().begin(), _sqrtEx2.variables().end() );
        SqrtEx result = SqrtEx( _sqrtEx2.denominator() * _sqrtEx1.constantPart() + _sqrtEx2.constantPart() * _sqrtEx1.denominator(),
                         _sqrtEx2.denominator() * _sqrtEx1.factor() + _sqrtEx2.factor() * _sqrtEx1.denominator(),
                         _sqrtEx1.denominator() * _sqrtEx2.denominator(), _sqrtEx1.radicand(), vars );
        return result;
    }

    /**
     * @param _sqrtEx1  Minuend.
     * @param _sqrtEx2  Subtrahend.
     *
     * @return Difference.
     */
    SqrtEx operator -( const SqrtEx& _sqrtEx1, const SqrtEx& _sqrtEx2 )
    {
        assert( !_sqrtEx1.hasSqrt() ||!_sqrtEx2.hasSqrt() || _sqrtEx1.radicand() == _sqrtEx2.radicand() );
        symtab vars = symtab( _sqrtEx1.variables() );
        vars.insert( _sqrtEx2.variables().begin(), _sqrtEx2.variables().end() );
        SqrtEx result = SqrtEx( _sqrtEx2.denominator() * _sqrtEx1.constantPart() - _sqrtEx2.constantPart() * _sqrtEx1.denominator(),
                         _sqrtEx2.denominator() * _sqrtEx1.factor() - _sqrtEx2.factor() * _sqrtEx1.denominator(),
                         _sqrtEx1.denominator() * _sqrtEx2.denominator(), _sqrtEx1.radicand(), vars );
        return result;
    }

    /**
     * @param _sqrtEx1  First factor.
     * @param _sqrtEx2  Second factor.
     *
     * @return Product.
     */
    SqrtEx operator *( const SqrtEx& _sqrtEx1, const SqrtEx& _sqrtEx2 )
    {
        assert( !_sqrtEx1.hasSqrt() ||!_sqrtEx2.hasSqrt() || _sqrtEx1.radicand() == _sqrtEx2.radicand() );
        symtab vars = symtab( _sqrtEx1.variables() );
        vars.insert( _sqrtEx2.variables().begin(), _sqrtEx2.variables().end() );
        SqrtEx result = SqrtEx( _sqrtEx2.constantPart() * _sqrtEx1.constantPart() + _sqrtEx2.factor() * _sqrtEx1.factor() * _sqrtEx1.radicand(),
                         _sqrtEx2.constantPart() * _sqrtEx1.factor() + _sqrtEx2.factor() * _sqrtEx1.constantPart(),
                         _sqrtEx1.denominator() * _sqrtEx2.denominator(), _sqrtEx1.radicand(), vars );
        return result;
    }

    /**
     * @param _sqrtEx1  Dividend.
     * @param _sqrtEx2  Divisor.
     *
     * @return  The result of this square root expression divided by the given on,
     *          which is not allowed to contain a square root itself.
     */
    SqrtEx operator /( const SqrtEx& _sqrtEx1, const SqrtEx& _sqrtEx2 )
    {
        assert( !_sqrtEx2.hasSqrt() );
        symtab vars = symtab( _sqrtEx1.variables() );
        vars.insert( _sqrtEx2.variables().begin(), _sqrtEx2.variables().end() );
        SqrtEx result = SqrtEx( _sqrtEx1.constantPart() * _sqrtEx2.denominator(), _sqrtEx1.factor() * _sqrtEx2.denominator(),
                         _sqrtEx1.denominator() * _sqrtEx2.factor(), _sqrtEx1.radicand(), vars );
        return result;
    }

    /**
     * Prints a square root expression on an output stream.
     *
     * @param   _ostream    The output stream, on which to write.
     * @param   _sqrtEx     The square root expression to print.
     *
     * @return The representation of the square root expression on an output stream.
     */
    ostream& operator <<( ostream& _ostream, const SqrtEx& _sqrtEx )
    {
        _ostream << "( (" << _sqrtEx.constantPart();
        _ostream << ") + (";
        _ostream << _sqrtEx.factor();
        _ostream << ") * ";
        _ostream << "sqrt(";
        _ostream << _sqrtEx.radicand();
        _ostream << ") )";
        _ostream << " / (";
        _ostream << _sqrtEx.denominator();
        _ostream << ")";
        return _ostream;
    }

    /**
     *
     * @param _expression
     * @param _var
     */
    void simplify( ex& _expression, const ex& _var )
    {
        if( _expression.has( _var ) )
        {
            ex un, con, prim;
            _expression.unitcontprim( _var, un, con, prim );
            if( con.info( info_flags::rational ) )
            {
                _expression = prim * un;
            }
        }
    }

    /**
     * Substitutes a variable in an expression by a square root expression, which
     * results in a square root expression.
     *
     * @param _ex       The expression to substitute in.
     * @param _var      The variable to substitute.
     * @param _subTerm  The square root expression by which the variable gets substituted.
     *
     * @return The resulting square root expression.
     */
    SqrtEx subBySqrtEx( const ex& _ex, const ex& _var, const SqrtEx& _subTerm, const symtab& _variables )
    {
        #ifdef VS_DEBUG_METHODS
        cout << "subBySqrtEx" << endl;
        #endif

        /*
         * We have to calculate the result of the substitution:
         *
         *                           q+r*sqrt{t}
         *        (a_n*x^n+...+a_0)[------------ / x]
         *                               s
         * being:
         *
         *      \sum_{k=0}^n (a_k * (q+r*sqrt{t})^k * s^{n-k})
         *      ----------------------------------------------
         *                           s^n
         */
        signed n = _ex.degree( _var );
        if( n == 0 )
        {
            SqrtEx result = SqrtEx( _ex.numer(), 0, _ex.denom(), 0, _variables );
            return result;
        }

        // Calculate the s^k:   (0<=k<=n)
        vector<ex> sk = vector<ex>( n + 1 );
        sk[0] = ex( 1 );
        for( signed i = 1; i <= n; i++ )
        {
            sk[i] = sk[i - 1] * _subTerm.denominator();
        }

        // Calculate the constant part and factor of the square root
        // of (q+r*sqrt{t})^k:   (1<=k<=n)
        vector<ex> qk = vector<ex>( n );
        vector<ex> rk = vector<ex>( n );
        qk[0] = ex( _subTerm.constantPart() );
        rk[0] = ex( _subTerm.factor() );
        for( signed i = 1; i < n; i++ )
        {
            qk[i] = _subTerm.constantPart() * qk[i - 1] + _subTerm.factor() * rk[i - 1] * _subTerm.radicand();
            rk[i] = _subTerm.constantPart() * rk[i - 1] + _subTerm.factor() * qk[i - 1];
        }
        // Calculate the result:
        ex resConstantPart = sk[n] * _ex.coeff( _var, 0 );
        ex resFactor       = 0;
        for( signed i = 1; i <= n; i++ )
        {
            resConstantPart += _ex.coeff( _var, i ) * qk[i - 1] * sk[n - i];
            resFactor       += _ex.coeff( _var, i ) * rk[i - 1] * sk[n - i];
        }
//        for( auto var = _variables.begin(); var != _variables.end(); ++var )
//        {
//            if( resConstantPart.has( var->second ) )
//            {
//                simplify( resConstantPart, var->second );
//                break;
//            }
//        }
//        for( auto var = _variables.begin(); var != _variables.end(); ++var )
//        {
//            if( resFactor.has( var->second ) )
//            {
//                simplify( resFactor, var->second );
//                break;
//            }
//        }
//        for( auto var = _variables.begin(); var != _variables.end(); ++var )
//        {
//            if( sk[n].has( var->second ) )
//            {
//                simplify( sk[n], var->second );
//                break;
//            }
//        }
//        ex radicand = _subTerm.radicand();
//        for( auto var = _variables.begin(); var != _variables.end(); ++var )
//        {
//            if( radicand.has( var->second ) )
//            {
//                simplify( radicand, var->second );
//                break;
//            }
//        }
        SqrtEx result = SqrtEx( resConstantPart, resFactor, sk[n], _subTerm.radicand(), _variables );
        return result;
    }
}    // end namspace vs

