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
 * @file Integer.h
 * @author Florian Corzilius
 *
 * @version 2012-04-05
 * Created on November 14th, 2012
 */

#ifndef INTEGER_H
#define	INTEGER_H

#include <ginac/ginac.h>
#include <sstream>

namespace tlra
{
    class Integer
    {
        private:
            /*
             * Members:
             */
            unsigned mNumerator;
            signed mDenominator;

        public:
            /*
             * Constructors and destructor:
             */
            Integer( const int );
            Integer( const GiNaC::numeric& );

            bool isNegative() const;
            bool isPositive() const;
            bool isZero() const;
            GiNaC::numeric ginacNumeric() const;

            /*
             * Operators:
             */
            Integer operator +( const Integer& ) const;
            void operator +=( const Integer& );
            friend Integer operator -( const Integer& );
            Integer operator -( const Integer& ) const;
            void operator -=( const Integer& );
            Integer operator *( const Integer& ) const;
            void operator *=( const Integer& );
            Integer operator /( const Integer& ) const;
            void operator /=( const Integer& );
            bool operator <( const Integer& ) const;
            bool operator >( const Integer& ) const;
            bool operator <=( const Integer& ) const;
            bool operator >=( const Integer& ) const;
            bool operator !=( const Integer& ) const;
            bool operator ==( const Integer& ) const;
            friend std::ostream& operator <<( std::ostream&, const Integer& );
    };
}    // end namspace tlra


#endif	/* INTEGER_H */

