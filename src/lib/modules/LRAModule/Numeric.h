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
 * @author Florian Corzilius
 *
 * @version 2012-04-05
 * Created on November 14th, 2012
 */

#ifndef NUMERIC_H
#define	NUMERIC_H

#include <ginac/ginac.h>
#include <sstream>

namespace lra
{
    class Numeric
    {
        private:
            /*
             * Members:
             */
            GiNaC::numeric* mpContent;

        public:
            /*
             * Constructors and destructor:
             */
            Numeric( const int );
            Numeric( const GiNaC::numeric& );

            const GiNaC::numeric& content() const
            {
                return *mpContent;
            }

            bool isNegative() const;
            bool isPositive() const;
            bool isZero() const;
            GiNaC::numeric ginacNumeric() const;

            /*
             * Operators:
             */
            Numeric operator +( const Numeric& ) const;
            void operator +=( const Numeric& );
            friend Numeric operator -( const Numeric& );
            Numeric operator -( const Numeric& ) const;
            void operator -=( const Numeric& );
            Numeric operator *( const Numeric& ) const;
            void operator *=( const Numeric& );
            Numeric operator /( const Numeric& ) const;
            void operator /=( const Numeric& );
            bool operator <( const Numeric& ) const;
            bool operator >( const Numeric& ) const;
            bool operator <=( const Numeric& ) const;
            bool operator >=( const Numeric& ) const;
            bool operator !=( const Numeric& ) const;
            bool operator ==( const Numeric& ) const;
            friend std::ostream& operator <<( std::ostream&, const Numeric& );
    };
}    // end namspace lra


#endif	/* NUMERIC_H */

