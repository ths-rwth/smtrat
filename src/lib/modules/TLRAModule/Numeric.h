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

#include <ginac/ginac.h>
#include <ginac/flags.h>
#include <iostream>
#include <assert.h>

namespace smtrat
{
    namespace tlra
    {
        class Numeric
        {
        private:
            // Members:
            std::shared_ptr<GiNaC::numeric> mContent;

        public:
            // Constructors/Destructor:
            Numeric();
            Numeric( const GiNaC::numeric& );
            Numeric( int );
            Numeric( unsigned int );
            Numeric( long );
            Numeric( unsigned long );
            Numeric( double );
            Numeric( const char* );
            Numeric( const cln::cl_N& );
            Numeric( const Numeric& );
            ~Numeric();

            // Methods:
            const GiNaC::numeric& content() const
            {
                return *mContent;
            }

            GiNaC::numeric& rContent()
            {
                return *mContent;
            }

            Numeric& operator=( int );
            Numeric& operator=( unsigned int );
            Numeric& operator=( long );
            Numeric& operator=( unsigned long );
            Numeric& operator=( double );
            Numeric& operator=( const char* );

            bool operator==( const Numeric& ) const;
            bool operator!=( const Numeric& ) const;
            bool operator<( const Numeric& ) const;
            bool operator<=( const Numeric& ) const;
            bool operator>( const Numeric& ) const;
            bool operator>=( const Numeric& ) const;

            int toInt() const;
            long toLong() const;
            double toDouble() const;
            cln::cl_N toCLN() const;
            GiNaC::numeric toGinacNumeric() const;
            Numeric numer() const;
            Numeric denom() const;

            bool isPositive() const;
            bool isNegative() const;
            bool isZero() const;
        };

        Numeric abs( const Numeric& );
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
    } // namespace tlra
} // namespace smtrat

#endif	/* NUMERIC_H */

