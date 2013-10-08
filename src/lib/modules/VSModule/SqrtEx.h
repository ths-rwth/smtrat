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

#ifndef SMTRAT_VS_SQRTEX_H
#define SMTRAT_VS_SQRTEX_H

#include <iostream>
#include <assert.h>
#include "../../Common.h"

namespace vs
{
    class SqrtEx
    {
        private:
            // Members:
            smtrat::Polynomial mConstantPart;
            smtrat::Polynomial mFactor;
            smtrat::Polynomial mDenominator;
            smtrat::Polynomial mRadicand;

        public:
            // Constructors:
            SqrtEx();
            SqrtEx( const smtrat::Polynomial& );
            SqrtEx( const smtrat::Polynomial&, const smtrat::Polynomial&, const smtrat::Polynomial&, const smtrat::Polynomial& );
            SqrtEx( const SqrtEx& );

            // Destructor:
            ~SqrtEx();

            // Methods:
            const smtrat::Polynomial& constantPart() const
            {
                return mConstantPart;
            }

            smtrat::Polynomial& rConstantPart()
            {
                return mConstantPart;
            }

            const smtrat::Polynomial& factor() const
            {
                return mFactor;
            }

            smtrat::Polynomial& rFactor()
            {
                return mFactor;
            }

            const smtrat::Polynomial& radicand() const
            {
                return mRadicand;
            }

            smtrat::Polynomial& rRadicand()
            {
                return mRadicand;
            }

            const smtrat::Polynomial& denominator() const
            {
                return mDenominator;
            }

            smtrat::Polynomial& rDenominator()
            {
                return mDenominator;
            }

            bool hasSqrt() const
            {
                return mFactor != smtrat::Polynomial( smtrat::Rational( 0 ) );
            }

            // Operators.
            bool operator ==( const SqrtEx& ) const;
            SqrtEx& operator = ( const SqrtEx& );
            SqrtEx& operator = ( const smtrat::Polynomial& );
            friend SqrtEx operator +( const SqrtEx&, const SqrtEx& );
            friend SqrtEx operator -( const SqrtEx&, const SqrtEx& );
            friend SqrtEx operator *( const SqrtEx&, const SqrtEx& );
            friend SqrtEx operator /( const SqrtEx&, const SqrtEx& );
            std::string toString( bool = false ) const;
            friend std::ostream& operator <<( std::ostream&, const SqrtEx& );
            static SqrtEx subBySqrtEx( const smtrat::Polynomial&, const carl::Variable&, const SqrtEx& );
        private:
            void normalize();
    };
}    // end namspace vs

#endif
