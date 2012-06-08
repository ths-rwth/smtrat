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
    }

    SqrtEx::SqrtEx( const GiNaC::ex& _ex )
    {
        mpConstantPart = new ex( _ex.numer() );
        mpFactor       = new ex( 0 );
        mpDenominator  = new ex( _ex.denom() );
        mpRadicand     = new ex( 0 );
    }

    SqrtEx::SqrtEx( const GiNaC::ex& _constantPart, const GiNaC::ex& _factor, const GiNaC::ex& _denominator, const GiNaC::ex& _radicand )
    {
        assert( _denominator != 0 );
        assert( !_radicand.info( info_flags::rational ) || _radicand.info( info_flags::nonnegative ));
        mpConstantPart = new ex( _constantPart );
        if( _radicand == 0 )
        {
            mpFactor = new ex( 0 );
        }
        else
        {
            mpFactor = new ex( _factor );
        }
        mpDenominator = new ex( _denominator );
        if( _factor == 0 )
        {
            mpRadicand = new ex( 0 );
        }
        else
        {
            mpRadicand = new ex( _radicand );
        }
    }

    SqrtEx::SqrtEx( const SqrtEx& _sqrtEx )
    {
        mpConstantPart = new ex( _sqrtEx.constantPart() );
        mpFactor       = new ex( _sqrtEx.factor() );
        mpDenominator  = new ex( _sqrtEx.denominator() );
        mpRadicand     = new ex( _sqrtEx.radicand() );
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
    bool SqrtEx::hasVariable( const ex& _variable ) const
    {
        if( constantPart().has( _variable ))
        {
            return true;
        }
        else if( factor().has( _variable ))
        {
            return true;
        }
        else if( radicand().has( _variable ))
        {
            return true;
        }
        else
            return denominator().has( _variable );
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
        SqrtEx
        result = SqrtEx( _sqrtEx2.denominator() * _sqrtEx1.constantPart() + _sqrtEx2.constantPart() * _sqrtEx1.denominator(),
                         _sqrtEx2.denominator() * _sqrtEx1.factor() + _sqrtEx2.factor() * _sqrtEx1.denominator(),
                         _sqrtEx1.denominator() * _sqrtEx2.denominator(), _sqrtEx1.radicand() );
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
        SqrtEx
        result = SqrtEx( _sqrtEx2.denominator() * _sqrtEx1.constantPart() - _sqrtEx2.constantPart() * _sqrtEx1.denominator(),
                         _sqrtEx2.denominator() * _sqrtEx1.factor() - _sqrtEx2.factor() * _sqrtEx1.denominator(),
                         _sqrtEx1.denominator() * _sqrtEx2.denominator(), _sqrtEx1.radicand() );
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
        SqrtEx
        result = SqrtEx( _sqrtEx2.constantPart() * _sqrtEx1.constantPart() + _sqrtEx2.factor() * _sqrtEx1.factor() * _sqrtEx1.radicand(),
                         _sqrtEx2.constantPart() * _sqrtEx1.factor() + _sqrtEx2.factor() * _sqrtEx1.constantPart(),
                         _sqrtEx1.denominator() * _sqrtEx2.denominator(), _sqrtEx1.radicand() );
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
        SqrtEx
        result = SqrtEx( _sqrtEx1.constantPart() * _sqrtEx2.denominator(), _sqrtEx1.factor() * _sqrtEx2.denominator(),
                         _sqrtEx1.denominator() * _sqrtEx2.factor(), _sqrtEx1.radicand() );
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

}    // end namspace vs

