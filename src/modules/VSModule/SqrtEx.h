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

#ifndef SMTRAT_VS_SQRTEX_H
#define SMTRAT_VS_SQRTEX_H
//#define VS_USE_GINAC_EXPAND
//#define VS_USE_GINAC_NORMAL

#include <ginac/ginac.h>
#include <ginac/flags.h>
#include <iostream>
#include <assert.h>

namespace vs
{
    class SqrtEx
    {
        public:

            /**
             * Constructors:
             */
            SqrtEx();
            SqrtEx( const GiNaC::ex& );
            SqrtEx( const GiNaC::ex&, const GiNaC::ex&, const GiNaC::ex&, const GiNaC::ex& );
            SqrtEx( const SqrtEx& );

            /**
             * Destructor:
             */
            ~SqrtEx();

            /**
             * Methods:
             */
            const GiNaC::ex& constantPart() const
            {
                return *mpConstantPart;
            }

            GiNaC::ex& rConstantPart()
            {
                return *mpConstantPart;
            }

            const GiNaC::ex& factor() const
            {
                return *mpFactor;
            }

            GiNaC::ex& rFactor()
            {
                return *mpFactor;
            }

            const GiNaC::ex& radicand() const
            {
                return *mpRadicand;
            }

            GiNaC::ex& rRadicand()
            {
                return *mpRadicand;
            }

            const GiNaC::ex& denominator() const
            {
                return *mpDenominator;
            }

            GiNaC::ex& rDenominator()
            {
                return *mpDenominator;
            }

            bool hasSqrt() const
            {
                return *mpFactor != 0;
            }

            static void normalize( GiNaC::ex& _exp )
            {
                #ifdef VS_USE_GINAC_NORMAL
                #ifdef VS_USE_GINAC_EXPAND
                _exp    = _exp.expand().normal();
                #else
                _exp    = _exp.normal();
                #endif
                #else
                #ifdef VS_USE_GINAC_EXPAND
                _exp    = _exp.expand();
                #endif
                #endif
            }

            // Data access methods (read only).
            bool hasVariable( const GiNaC::ex& ) const;
            GiNaC::ex expression() const;

            // Operators.
            bool operator ==( const SqrtEx& ) const;
            SqrtEx& operator = ( const SqrtEx& );
            SqrtEx& operator = ( const GiNaC::ex& );
            friend SqrtEx operator +( const SqrtEx&, const SqrtEx& );
            friend SqrtEx operator -( const SqrtEx&, const SqrtEx& );
            friend SqrtEx operator *( const SqrtEx&, const SqrtEx& );
            friend SqrtEx operator /( const SqrtEx&, const SqrtEx& );
            friend std::ostream& operator <<( std::ostream&, const SqrtEx& );

        private:

            /**
             * Attributes:
             */
            GiNaC::ex* mpConstantPart;
            GiNaC::ex* mpFactor;
            GiNaC::ex* mpRadicand;
            GiNaC::ex* mpDenominator;
    };
    SqrtEx subBySqrtEx( const GiNaC::ex&, const GiNaC::ex&, const SqrtEx& );
}    // end namspace vs

#endif
