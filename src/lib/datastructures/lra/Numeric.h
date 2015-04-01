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
 * @file Numeric.h
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2013-04-15
 * Created on April 15th, 2013
 */

#ifndef NUMERIC_H
#define	NUMERIC_H

#include <iostream>
#include <assert.h>
#include "../../Common.h"

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

            bool isPositive() const;
            bool isNegative() const;
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

