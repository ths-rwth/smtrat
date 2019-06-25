/**
 * @file Numeric.cpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2013-04-15
 * Created on April 15th, 2013
 */

#include "Numeric.h"

namespace smtrat
{
    namespace lra
    {
        /**
         * Default constructor.
         */
        Numeric::Numeric():
            mContent( new Rational( 0 ) )
        {}

        /**
         * Constructing from a Rational.
         * @param The Rational.
         */
        Numeric::Numeric( const Rational& _value ):
            mContent( new Rational( _value ) )
        {}

        /**
         * Constructing from an integer.
         * @param _value The integer.
         */
        Numeric::Numeric( int _value ):
            mContent( new Rational( _value ) )
        {}

        /**
         * Constructing from an unsigned integer.
         * @param _value The unsigned integer
         */
        Numeric::Numeric( unsigned int _value ):
            mContent( new Rational( _value ) )
        {}

        /**
         * Constructing from a long integer.
         * @param _value The unsigned long integer.
         */
        Numeric::Numeric( long _value ):
            mContent( new Rational( _value ) )
        {}

        /**
         * Constructing from an unsigned long integer.
         * @param _value The unsigned long integer.
         */
        Numeric::Numeric( unsigned long _value ):
            mContent( new Rational( _value ) )
        {}

        /**
         * Constructing from a char array.
         * @param _value The char array.
         */
        Numeric::Numeric( const char* _value ):
            mContent( new Rational( _value ) )
        {}

        /**
         * Copy constructor.
         * @param _value The Numeric to copy.
         */
        Numeric::Numeric( const Numeric& _value ):
            mContent( new Rational( *_value.mContent ) )
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
         * @return The enumerator of this Numeric.
         */
        Numeric Numeric::numer() const
        {
            return Numeric( carl::getNum( this->content() ) );
        }

        /**
         * @return The denominator of this Numeric.
         */
        Numeric Numeric::denom() const
        {
            return Numeric( carl::getDenom( this->content() ) );
        }
        
        /**
         * @return The next smaller integer to this Numeric.
         */
        Numeric Numeric::floor() const
        {
            return Numeric( carl::floor( this->content() ) );
        }

        /**
         * Checks whether this Numeric corresponds to a positive rational number.
         * @return True, if this Numeric corresponds to a positive rational number;
         *          False, otherwise.
         */
        bool Numeric::isPositive() const
        {
            return ( this->content() > 0 );
        }

        /**
         * @return true, if this Numeric corresponds to a positive rational number;
         *         false, otherwise.
         */
        bool Numeric::isNegative() const
        {
            return ( this->content() < 0 );
        }

        /**
         * @return true, if this Numeric corresponds to zero;
         *         false, otherwise.
         */
        bool Numeric::isZero() const
        {
            return ( this->content() == 0 );
        }

        /**
         * @return true, if this Numeric is integer;
         *         false, otherwise.
         */
        bool Numeric::isInteger() const
        {
            return ( this->denom() == 1 );
        }

        /**
         * Calculates the absolute value of the given Numeric.
         * @param _value The Numeric to calculate the Numeric for.
         * @return The absolute value of the given Numeric.
         */
        Numeric abs( const Numeric& _value )
        {
            return Numeric( carl::abs( _value.content() ) );
        }
        
        /**
         * Calculates the result of the first argument modulo the second argument.
         * Note, that this method can only be applied to integers.
         * @param _valueA An integer.
         * @param _valueB An integer != 0.
         * @return The first argument modulo the second argument.
         */
        Numeric mod( const Numeric& _valueA, const Numeric& _valueB )
        {
            assert( _valueA.isInteger() && _valueB.isInteger() );
            assert( !_valueB.isZero() );
            return Numeric( carl::mod( carl::getNum( _valueA.content() ), carl::getNum( _valueB.content() ) ) );
        }
        
        /**
         * Calculates the least common multiple of the two arguments.
         * Note, that this method can only be applied to integers.
         * @param _valueA An integer.
         * @param _valueB An integer.
         * @return The least common multiple of the two arguments.
         */
        Numeric lcm( const Numeric& _valueA, const Numeric& _valueB )
        {
            assert( _valueA.isInteger() && _valueB.isInteger() );
            if( _valueA.isZero() || _valueB.isZero() )
                return Numeric( 0 );
            return Numeric( carl::lcm( carl::getNum( _valueA.content() ), carl::getNum( _valueB.content() ) ) );
        }
        
        /**
         * Calculates the greatest common divisor of the two arguments.
         * Note, that this method can only be applied to integers.
         * @param _valueA An integer.
         * @param _valueB An integer.
         * @return The least common divisor of the two arguments.
         */
        Numeric gcd( const Numeric& _valueA, const Numeric& _valueB )
        {
            assert( _valueA.isInteger() && _valueB.isInteger() );
            if( _valueA.isZero() || _valueB.isZero() )
                return Numeric( 0 );
            return Numeric( carl::gcd( carl::getNum( _valueA.content() ), carl::getNum( _valueB.content() ) ) );
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
        std::ostream& operator <<( std::ostream& _out, const Numeric& _value )
        {
            _out << _value.content();
            return _out;
        }
    } // end namespace lra
} // end namespace smtrat
