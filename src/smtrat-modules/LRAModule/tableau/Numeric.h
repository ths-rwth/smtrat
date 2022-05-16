/**
 * @file Numeric.h
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2013-04-15
 * Created on April 15th, 2013
 */

#ifndef NUMERIC_H
#define	NUMERIC_H

#include <iostream>
#include <cassert>
#include <smtrat-common/smtrat-common.h>


namespace smtrat
{
    namespace lra
    {
        class Numeric
        {
        private:
            // Members:
            Rational* mContent;

        public:
            // Constructors/Destructor:
            Numeric();
            Numeric( const Rational& );
            Numeric( int );
            Numeric( unsigned int );
            Numeric( long );
            Numeric( unsigned long );
            Numeric( const char* );
            Numeric( const Numeric& );
            ~Numeric();

            // Methods:
            const Rational& content() const
            {
                return *mContent;
            }

            Rational& rContent()
            {
                return *mContent;
            }

            Numeric& operator=( int );
            Numeric& operator=( unsigned int );
            Numeric& operator=( long );
            Numeric& operator=( unsigned long );
            Numeric& operator=( const char* );
            Numeric& operator=( const Numeric& );

            bool operator==( const Numeric& ) const;
            bool operator!=( const Numeric& ) const;
            bool operator<( const Numeric& ) const;
            bool operator<=( const Numeric& ) const;
            bool operator>( const Numeric& ) const;
            bool operator>=( const Numeric& ) const;

            Numeric numer() const;
            Numeric denom() const;
            Numeric floor() const;

            bool is_positive() const;
            bool is_negative() const;
            bool isZero() const;
            bool isInteger() const;
        };

        Numeric abs( const Numeric& );
        Numeric mod( const Numeric&, const Numeric& );
        Numeric lcm( const Numeric&, const Numeric& );
        Numeric gcd( const Numeric&, const Numeric& );
        Numeric operator+( const Numeric&, const Numeric& );
        Numeric operator-( const Numeric&, const Numeric& );
        Numeric operator*( const Numeric&, const Numeric& );
        Numeric operator/( const Numeric&, const Numeric& );
        Numeric& operator+=( Numeric&, const Numeric& );
        Numeric& operator-=( Numeric&, const Numeric& );
        Numeric& operator*=( Numeric&, const Numeric& );
        Numeric& operator/=( Numeric&, const Numeric& );
        Numeric operator-( const Numeric& );
        Numeric& operator++( Numeric& );
        Numeric& operator--( Numeric& );
        std::ostream& operator <<( std::ostream&, const Numeric& );
    } // namespace lra
} // namespace smtrat

#endif	/* NUMERIC_H */

