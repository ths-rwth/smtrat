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
 * @version 2013-10-07
 */

#include "SqrtEx.h"

namespace vs
{
    using namespace std;

    /**
     * Constructors:
     */
    SqrtEx::SqrtEx():
        mConstantPart( smtrat::ZERO_RATIONAL ),
        mFactor( smtrat::ZERO_RATIONAL ),
        mDenominator( smtrat::ONE_RATIONAL ),
        mRadicand( smtrat::ZERO_RATIONAL )
    {}

    SqrtEx::SqrtEx( const smtrat::Polynomial& _poly ):
        mConstantPart( _poly ),
        mFactor( smtrat::ZERO_RATIONAL ),
        mDenominator( smtrat::ONE_RATIONAL ),
        mRadicand( smtrat::ZERO_RATIONAL )
    {
        normalize();
    }

    SqrtEx::SqrtEx( const smtrat::Polynomial& _constantPart, const smtrat::Polynomial& _factor, const smtrat::Polynomial& _denominator, const smtrat::Polynomial& _radicand ):
        mConstantPart( _constantPart ),
        mFactor( _radicand == smtrat::ZERO_POLYNOMIAL ? smtrat::ZERO_POLYNOMIAL : _factor ),
        mDenominator( ((mFactor == smtrat::ZERO_POLYNOMIAL) && (_constantPart == smtrat::ZERO_POLYNOMIAL)) ? smtrat::ONE_POLYNOMIAL : _denominator ),
        mRadicand( ( _factor == smtrat::ZERO_POLYNOMIAL ) ? smtrat::ZERO_POLYNOMIAL : _radicand )
    {
        assert( _denominator != smtrat::ZERO_POLYNOMIAL );
        assert( !_radicand.isConstant() || smtrat::ZERO_RATIONAL <= _radicand.trailingTerm()->coeff() );
        normalize();
    }

    SqrtEx::SqrtEx( const SqrtEx& _sqrtEx ):
        mConstantPart( _sqrtEx.constantPart() ),
        mFactor( _sqrtEx.factor() ),
        mDenominator( _sqrtEx.denominator() ),
        mRadicand( _sqrtEx.radicand() )
    {}

    /**
     * Destructor:
     */
    SqrtEx::~SqrtEx()
    {}

    /**
     * Normalizes this object, that is extracts as much as possible from the radicand into the factor
     * and cancels the enumerator and denominator afterwards.
     */
    void SqrtEx::normalize()
    {
        //TODO: implement this method
    }
    
    /**
     * @param _sqrtEx Square root expression to compare with.
     * @return  true, if this square root expression and the given one are equal;
     *          false, otherwise.
     */
    bool SqrtEx::operator ==( const SqrtEx& _sqrtEx ) const
    {
        if( mRadicand == _sqrtEx.radicand() )
            if( mDenominator == _sqrtEx.denominator() )
                if( mFactor == _sqrtEx.factor() )
                    if( mConstantPart == _sqrtEx.constantPart() )
                        return true;
        return false;
    }

    /**
     * @param _sqrtEx A square root expression, which gets the new content of this square root expression.
     * @return A reference to this object.
     */
    SqrtEx& SqrtEx::operator = ( const SqrtEx& _sqrtEx )
    {
        if( this != &_sqrtEx )
        {
            mConstantPart = _sqrtEx.constantPart();
            mFactor       = _sqrtEx.factor();
            mDenominator  = _sqrtEx.denominator();
            if( factor() == smtrat::ZERO_POLYNOMIAL )
                mRadicand = smtrat::ZERO_POLYNOMIAL;
            else
                mRadicand = _sqrtEx.radicand();
        }
        return *this;
    }

    /**
     * @param _poly A polynomial, which gets the new content of this square root expression.
     * @return A reference to this object.
     */
    SqrtEx& SqrtEx::operator = ( const smtrat::Polynomial& _poly )
    {
        mConstantPart = _poly;
        mFactor       = smtrat::ZERO_POLYNOMIAL;
        mDenominator  = smtrat::ONE_POLYNOMIAL;
        mRadicand     = smtrat::ZERO_POLYNOMIAL;
        return *this;
    }

    /**
     * @param _sqrtEx1  First summand.
     * @param _sqrtEx2  Second summand.
     * @return The sum of the given square root expressions.
     */
    SqrtEx operator +( const SqrtEx& _sqrtEx1, const SqrtEx& _sqrtEx2 )
    {
        assert( !_sqrtEx1.hasSqrt() ||!_sqrtEx2.hasSqrt() || _sqrtEx1.radicand() == _sqrtEx2.radicand() );
        SqrtEx result = SqrtEx( _sqrtEx2.denominator() * _sqrtEx1.constantPart() + _sqrtEx2.constantPart() * _sqrtEx1.denominator(),
                         _sqrtEx2.denominator() * _sqrtEx1.factor() + _sqrtEx2.factor() * _sqrtEx1.denominator(),
                         _sqrtEx1.denominator() * _sqrtEx2.denominator(), _sqrtEx1.radicand() );
        return result;
    }

    /**
     * @param _sqrtEx1  Minuend.
     * @param _sqrtEx2  Subtrahend.
     * @return The difference of the given square root expressions.
     */
    SqrtEx operator -( const SqrtEx& _sqrtEx1, const SqrtEx& _sqrtEx2 )
    {
        assert( !_sqrtEx1.hasSqrt() || !_sqrtEx2.hasSqrt() || _sqrtEx1.radicand() == _sqrtEx2.radicand() );
        SqrtEx result = SqrtEx( _sqrtEx2.denominator() * _sqrtEx1.constantPart() - _sqrtEx2.constantPart() * _sqrtEx1.denominator(),
                         _sqrtEx2.denominator() * _sqrtEx1.factor() - _sqrtEx2.factor() * _sqrtEx1.denominator(),
                         _sqrtEx1.denominator() * _sqrtEx2.denominator(), _sqrtEx1.radicand() );
        return result;
    }

    /**
     * @param _sqrtEx1  First factor.
     * @param _sqrtEx2  Second factor.
     * @return The product of the given square root expressions.
     */
    SqrtEx operator *( const SqrtEx& _sqrtEx1, const SqrtEx& _sqrtEx2 )
    {
        assert( !_sqrtEx1.hasSqrt() || !_sqrtEx2.hasSqrt() || _sqrtEx1.radicand() == _sqrtEx2.radicand() );
        SqrtEx result = SqrtEx( _sqrtEx2.constantPart() * _sqrtEx1.constantPart() + _sqrtEx2.factor() * _sqrtEx1.factor() * _sqrtEx1.radicand(),
                         _sqrtEx2.constantPart() * _sqrtEx1.factor() + _sqrtEx2.factor() * _sqrtEx1.constantPart(),
                         _sqrtEx1.denominator() * _sqrtEx2.denominator(), _sqrtEx1.radicand() );
        return result;
    }

    /**
     * @param _sqrtEx1  Dividend.
     * @param _sqrtEx2  Divisor.
     * @return The result of the first given square root expression divided by the second one
     *          Note that the second argument is not allowed to contain a square root.
     */
    SqrtEx operator /( const SqrtEx& _sqrtEx1, const SqrtEx& _sqrtEx2 )
    {
        assert( !_sqrtEx2.hasSqrt() );
        SqrtEx result = SqrtEx( _sqrtEx1.constantPart() * _sqrtEx2.denominator(), _sqrtEx1.factor() * _sqrtEx2.denominator(),
                         _sqrtEx1.denominator() * _sqrtEx2.factor(), _sqrtEx1.radicand() );
        return result;
    }
    
    /**
     * @param _infix A flag indicating whether to represent this square root expression 
     *         in infix notation (true) or prefix notation (false).
     * @return 
     */
    string SqrtEx::toString( bool _infix, bool _friendlyNames ) const
    {
        if( _infix )
        {
            string result = "((";
            result += mConstantPart.toString( true, _friendlyNames );
            result +=  ")+(";
            result +=  mFactor.toString( true, _friendlyNames );
            result +=  ")*";
            result +=  "sqrt(";
            result +=  mRadicand.toString( true, _friendlyNames );
            result +=  "))";
            result +=  "/(";
            result +=  mDenominator.toString( true, _friendlyNames );
            result +=  ")";
            return result;
        }
        else
        {
            string result = "(/ (+";
            result += mConstantPart.toString( false, _friendlyNames );
            result +=  " (*";
            result +=  mFactor.toString( false, _friendlyNames );
            result +=  " ";
            result +=  "(sqrt ";
            result +=  mRadicand.toString( false, _friendlyNames );
            result +=  "))) ";
            result +=  mDenominator.toString( false, _friendlyNames );
            result +=  ")";
            return result;
        }
    }

    /**
     * Prints a square root expression on an output stream.
     * @param   _ostream    The output stream, on which to write.
     * @param   _sqrtEx     The square root expression to print.
     * @return The representation of the square root expression on an output stream.
     */
    ostream& operator <<( ostream& _ostream, const SqrtEx& _sqrtEx )
    {
        return (_ostream << _sqrtEx.toString( true ) );
    }

    /**
     * Substitutes a variable in an expression by a square root expression, which
     * results in a square root expression.
     * @param _poly     The polynomial to substitute in.
     * @param _var      The variable to substitute.
     * @param _subTerm  The square root expression by which the variable gets substituted.
     * @return The resulting square root expression.
     */
    SqrtEx SqrtEx::subBySqrtEx( const smtrat::Polynomial& _poly, const carl::Variable& _var, const SqrtEx& _subTerm )
    {
        /*
         * We have to calculate the result of the substitution:
         *
         *                           q+r*sqrt{t}
         *        (a_n*x^n+...+a_0)[------------ / x]
         *                               s
         * being:
         *
         *      sum_{k=0}^n (a_k * (q+r*sqrt{t})^k * s^{n-k})
         *      ----------------------------------------------
         *                           s^n
         */
//        carl::VariableInformation<true,smtrat::Polynomial> varInfo = _poly.getVarInfo( _var ); //TODO: implement this line
        unsigned n = 0; // varInfo.maxDegree(); //TODO: implement this line
        if( n == 0 )
        {
            SqrtEx result = SqrtEx( _poly );
            return result;
        }
        // Calculate the s^k:   (0<=k<=n)
        vector<smtrat::Polynomial> sk = vector<smtrat::Polynomial>( n + 1 );
        sk[0] = smtrat::Polynomial( 1 );
        for( unsigned i = 1; i <= n; ++i )
            sk[i] = sk[i - 1] * _subTerm.denominator();
        // Calculate the constant part and factor of the square root of (q+r*sqrt{t})^k:   (1<=k<=n)
        vector<smtrat::Polynomial> qk = vector<smtrat::Polynomial>( n );
        vector<smtrat::Polynomial> rk = vector<smtrat::Polynomial>( n );
        qk[0] = smtrat::Polynomial( _subTerm.constantPart() );
        rk[0] = smtrat::Polynomial( _subTerm.factor() );
        for( unsigned i = 1; i < n; ++i )
        {
            qk[i] = _subTerm.constantPart() * qk[i - 1] + _subTerm.factor() * rk[i - 1] * _subTerm.radicand();
            rk[i] = _subTerm.constantPart() * rk[i - 1] + _subTerm.factor() * qk[i - 1];
        }
        // Calculate the result:
        smtrat::Polynomial resConstantPart = sk[n]; // * varInfo.coeffs( 0 ); //TODO: implement this line
        smtrat::Polynomial resFactor       = smtrat::ZERO_POLYNOMIAL;
        for( unsigned i = 1; i <= n; ++i )
        {
//            resConstantPart += varInfo.coeffs( i ) * qk[i - 1] * sk[n - i]; //TODO: implement this line
//            resFactor       += varInfo.coeffs( i ) * rk[i - 1] * sk[n - i]; //TODO: implement this line
        }
        SqrtEx result = SqrtEx( resConstantPart, resFactor, sk[n], _subTerm.radicand() );
        return result;
    }
}    // end namspace vs

