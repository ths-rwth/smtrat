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
 * @file Numeric.cpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2013-04-15
 * Created on April 15th, 2013
 */

#include <ginacra/settings.h>

#include "Numeric.h"

using namespace smtrat;
using namespace std;
using namespace GiNaC;

namespace smtrat
{
    namespace lra
    {
        /**
         * Default constructor.
         */
        Numeric::Numeric():
            mContent( new numeric( 0 ) )
        {}

        /**
         * Constructing from a GiNaC::numeric.
         * @param The GiNaC::numeric.
         */
        Numeric::Numeric( const numeric& _value ):
            mContent( new numeric( _value ) )
        {}

        /**
         * Constructing from an integer.
         * @param _value The integer.
         */
        Numeric::Numeric( int _value ):
            mContent( new numeric( _value ) )
        {}

        /**
         * Constructing from an unsigned integer.
         * @param _value The unsigned integer
         */
        Numeric::Numeric( unsigned int _value ):
            mContent( new numeric( _value ) )
        {}

        /**
         * Constructing from a long integer.
         * @param _value The unsigned long integer.
         */
        Numeric::Numeric( long _value ):
            mContent( new numeric( _value ) )
        {}

        /**
         * Constructing from an unsigned long integer.
         * @param _value The unsigned long integer.
         */
        Numeric::Numeric( unsigned long _value ):
            mContent( new numeric( _value ) )
        {}

        /**
         * Constructing from a double.
         * @param _value The double.
         */
        Numeric::Numeric( double _value ):
            mContent( new numeric( _value ) )
        {}

        /**
         * Constructing from a char array.
         * @param _value The char array.
         */
        Numeric::Numeric( const char* _value ):
            mContent( new numeric( _value ) )
        {}

        /**
         * Constructing from a CLN.
         * @param _value The CLN.
         */
        Numeric::Numeric( const cln::cl_N& _value ):
            mContent( new numeric( _value ) )
        {}

        /**
         * Copy constructor.
         * @param _value The Numeric to copy.
         */
        Numeric::Numeric( const Numeric& _value ):
            mContent( new numeric( *_value.mContent ) )
        {}

        Numeric::~Numeric()
        {
            delete mContent;
        }

        /**
         * Cast from an integer.
         * @param _value The integer.
         * @return The corresponding Numeric.
         */
        Numeric& Numeric::operator=( int _value )
        {
            return operator=( Numeric( _value ) );
        }

        /**
         * Cast from an unsigned inteeger.
         * @param _value The unsigned integer.
         * @return The corresponding Numeric.
         */
        Numeric& Numeric::operator=( unsigned int _value )
        {
            return operator=( Numeric( _value ) );
        }

        /**
         * Cast from a long integer.
         * @param _value The long integer.
         * @return The corresponding Numeric.
         */
        Numeric& Numeric::operator=( long _value )
        {
            return operator=( Numeric( _value ) );
        }

        /**
         * Cast from an unsigned long integer.
         * @param _value The unsigned long integer.
         * @return The corresponding Numeric.
         */
        Numeric& Numeric::operator=( unsigned long _value )
        {
            return operator=( Numeric( _value ) );
        }

        /**
         * Cast from a double.
         * @param _value The double.
         * @return The corresponding Numeric.
         */
        Numeric& Numeric::operator=( double _value )
        {
            return operator=( Numeric( _value ) );
        }

        /**
         * Cast from a char array.
         * @param _value The char array.
         * @return The corresponding Numeric.
         */
        Numeric& Numeric::operator=( const char* _value )
        {
            return operator=( Numeric( _value ) );
        }

        /**
         * Cast from a char array.
         * @param _value The char array.
         * @return The corresponding Numeric.
         */
        Numeric& Numeric::operator=( const Numeric& _value )
        {
            *mContent = _value.content();
            return *this;
        }

        /**
         * Compares whether this Numeric and the given one are equal.
         * @param _value The Numeric to compare with.
         * @return True, if the two Numerics are equal;
         *          False, otherwise.
         */
        bool Numeric::operator==( const Numeric& _value ) const
        {
            return this->content() == _value.content();
        }

        /**
         * Compares whether this Numeric and the given one are not equal.
         * @param _value The Numeric to compare with.
         * @return True, if the two Numerics are not equal;
         *          False, otherwise.
         */
        bool Numeric::operator!=( const Numeric& _value ) const
        {
            return this->content() != _value.content();
        }

        /**
         * Compares whether this Numeric is less than the given one.
         * @param _value The Numeric to compare with.
         * @return True, if this Numeric is less than the given one;
         *          False, otherwise.
         */
        bool Numeric::operator<( const Numeric& _value ) const
        {
            return this->content() < _value.content();
        }

        /**
         * Compares whether this Numeric is less or equal than the given one.
         * @param _value The Numeric to compare with.
         * @return True, if this Numeric is less or equal than the given one;
         *          False, otherwise.
         */
        bool Numeric::operator<=( const Numeric& _value ) const
        {
            return this->content() <= _value.content();
        }

        /**
         * Compares whether this Numeric is greater than the given one.
         * @param _value The Numeric to compare with.
         * @return True, if this Numeric is greater than the given one;
         *          False, otherwise.
         */
        bool Numeric::operator>( const Numeric& _value ) const
        {
            return this->content() > _value.content();
        }

        /**
         * Compares whether this Numeric is greater or equal than the given one.
         * @param _value The Numeric to compare with.
         * @return True, if this Numeric is greater or equal than the given one;
         *          False, otherwise.
         */
        bool Numeric::operator>=( const Numeric& _value ) const
        {
            return this->content() >= _value.content();
        }

        /**
         * Cast to integer.
         * @return This Numeric represented by an integer.
         */
        int Numeric::toInt() const
        {
            return this->content().to_int();
        }

        /**
         * Cast to long integer.
         * @return This Numeric represented by a long integer.
         */
        long Numeric::toLong() const
        {
            return this->content().to_long();
        }

        /**
         * Cast to double.
         * @return This Numeric represented by a double.
         */
        double Numeric::toDouble() const
        {
            return this->content().to_double();
        }

        /** 
         *  Returns a new CLN object of type cl_N, representing the value of *this.
         *  This method may be used when mixing GiNaC and CLN in one project.
         */
        cln::cl_N Numeric::toCLN() const
        {
            return this->content().to_cl_N();
        }

        /**
         * 
         * @return 
         */
        numeric Numeric::toGinacNumeric() const
        {
            return this->content();
        }

        /**
         * @return The enumerator of this Numeric.
         */
        Numeric Numeric::numer() const
        {
            return Numeric( this->content().numer() );
        }

        /**
         * @return The denominator of this Numeric.
         */
        Numeric Numeric::denom() const
        {
            return Numeric( this->content().denom() );
        }

        /**
         * Checks whether this Numeric corresponds to a positive rational number.
         * @return True, if this Numeric corresponds to a positive rational number;
         *          False, otherwise.
         */
        bool Numeric::isPositive() const
        {
            return this->content().is_positive();
        }

        /**
         * Checks whether this Numeric corresponds to a positive rational number.
         * @return True, if this Numeric corresponds to a positive rational number;
         *          False, otherwise.
         */
        bool Numeric::isNegative() const
        {
            return this->content().is_negative();
        }

        /**
         * Checks whether this Numeric corresponds to zero.
         * @return True, if this Numeric corresponds to zero;
         *          False, otherwise.
         */
        bool Numeric::isZero() const
        {
            return this->content().is_zero();
        }

        /**
         * Calculates the absolute value of the given Numeric.
         * @param _value The Numeric to calculate the Numeric for.
         * @return The absolute value of the given Numeric.
         */
        Numeric abs( const Numeric& _value )
        {
            return Numeric( abs( _value.content() ) );
        }

        /**
         * Calculates the sum of the two given Numerics.
         * @param _valueA The first summand.
         * @param _valueB The second summand.
         * @return The sum of the two given Numerics.
         */
        Numeric operator+( const Numeric& _valueA, const Numeric& _valueB )
        {
            return Numeric( _valueA.content() + _valueB.content() );
        }

        /**
         * Calculates the difference between the two given Numerics.
         * @param _valueA The minuend.
         * @param _valueB The subtrahend.
         * @return The difference between the two given Numerics.
         */
        Numeric operator-( const Numeric& _valueA, const Numeric& _valueB )
        {
            return Numeric( _valueA.content() - _valueB.content() );
        }

        /**
         * Calculates the product of the two given Numerics.
         * @param _valueA The first factor.
         * @param _valueB The second factor.
         * @return The product of the two given Numerics.
         */
        Numeric operator*( const Numeric& _valueA, const Numeric& _valueB )
        {
            return Numeric( _valueA.content() * _valueB.content() );
        }

        /**
         * Calculates the division of the two given Numerics.
         * @param _valueA The dividend.
         * @param _valueB The divisor.
         * @return The difference of the two given Numerics.
         */
        Numeric operator/( const Numeric& _valueA, const Numeric& _valueB )
        {
            return Numeric( _valueA.content() / _valueB.content() );    
        }

        /**
         * Adds the value of the second given Numeric to the second given Numeric.
         * @param _valueA The Numeric to add to.
         * @param _valueB The Numeric to add.
         * @return The first given Numeric increased by the second given Numeric.
         */
        Numeric& operator+=( Numeric& _valueA, const Numeric& _valueB )
        {
            _valueA.rContent() += _valueB.content();
            return _valueA;
        }

        /**
         * Subtracts the second given Numeric to the first given Numeric.
         * @param _valueA The Numeric to subtract from.
         * @param _valueB The Numeric to subtract.
         * @return The first given Numeric subtracted by the second given Numeric.
         */
        Numeric& operator-=( Numeric& _valueA, const Numeric& _valueB )
        {
            _valueA.rContent() -= _valueB.content();
            return _valueA;
        }

        /**
         * Multiplies the second given Numeric to the first given Numeric.
         * @param _valueA The Numeric to multiply.
         * @param _valueB The Numeric to multiply by.
         * @return The first given Numeric multiplied by the second given Numeric.
         */
        Numeric& operator*=( Numeric& _valueA, const Numeric& _valueB )
        {
            _valueA.rContent() *= _valueB.content();
            return _valueA;
        }

        /**
         * Divides the first given Numeric by the second given Numeric.
         * @param _valueA The Numeric to divide.
         * @param _valueB The Numeric to divide by.
         * @return The first given Numeric divided by the second given Numeric.
         */
        Numeric& operator/=( Numeric& _valueA, const Numeric& _valueB )
        {
            _valueA.rContent() /= _valueB.content();
            return _valueA;
        }

        /**
         * Calculates the additive inverse of the given Numeric.
         * @param _value The Numeric to calculate the additive inverse for.
         * @return The additive inverse of the given Numeric.
         */
        Numeric operator-( const Numeric& _value )
        {
            return Numeric( -_value.content() );
        }

        /**
         * Increments the given Numeric by one.
         * @param _value The Numeric to increment.
         * @return The given Numeric incremented by one.
         */
        Numeric& operator++( Numeric& _value )
        {
            _value.rContent()++;
            return _value;
        }

        /**
         * Decrements the given Numeric by one.
         * @param _value The Numeric to decrement.
         * @return The given Numeric decremented by one.
         */
        Numeric& operator--( Numeric& _value )
        {
            _value.rContent()--;
            return _value;
        }

        /**
         * Prints the given Numerics representation on the given output stream.
         * @param _out The output stream to print on.
         * @param _value The Numeric to print.
         * @return The output stream after printing the given Numerics representation on it.
         */
        ostream& operator <<( ostream& _out, const Numeric& _value )
        {
            _out << ex( _value.content() );
            return _out;
        }
    } // end namespace lra
} // end namespace smtrat
