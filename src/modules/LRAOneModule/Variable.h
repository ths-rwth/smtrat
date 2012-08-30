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
 * @file Variable.h
 * @author name surname <emailadress>
 *
 * @version 2012-04-05
 * Created on April 5th, 2012, 3:22 PM
 */

#ifndef _VARIABLE_H
#define _VARIABLE_H

#include "Bound.h"
#include <vector>
#include <map>

namespace lraone
{
    struct boundComp
    {
        bool operator ()( const Bound* const pBoundA, const Bound* const pBoundB ) const
        {
            return (*pBoundA) < (*pBoundB);
        }
    };

    typedef std::map<const Bound*, unsigned, boundComp> BoundActivityMap;

    class Variable
    {
        private:

            /**
             * Members.
             */
            Value             mAssignment;
            bool              mBasic;       // False nonbasic, True basic
            unsigned          mPosition;    // Number of Row or Column
            BoundActivityMap  mUpperbounds; // Know number of bounds for size of vector beforehand
            BoundActivityMap  mLowerbounds; // Maybe wait until last inform, pushbacktrackpoint() marks the last inform
            const Bound*      mpSupremum;
            const Bound*      mpInfimum;
            const GiNaC::ex*  mExpression;

        public:
            Variable();
            Variable( unsigned, bool, const GiNaC::ex* );
            virtual ~Variable();

            const Value& assignment() const
            {
                return mAssignment;
            }

            Value& rAssignment()
            {
                return mAssignment;
            }

            void setBasic( bool _basic )
            {
                mBasic = _basic;
            }

            bool getBasic()
            {
                return mBasic;
            }

            void setSupremum( const Bound* _supremum )
            {
                mpSupremum = _supremum;
            }

            const Bound* pSupremum() const
            {
                return mpSupremum;
            }

            const Bound& supremum() const
            {
                return *mpSupremum;
            }

            void setInfimum( const Bound* _infimum )
            {
                mpInfimum = _infimum;
            }

            const Bound* pInfimum() const
            {
                return mpInfimum;
            }

            const Bound& infimum() const
            {
                return *mpInfimum;
            }

            const unsigned position() const
            {
                return mPosition;
            }

            unsigned rLowerBoundsSize()
            {
                return mLowerbounds.size();
            }

            unsigned rUpperBoundsSize()
            {
                return mUpperbounds.size();
            }

            const BoundActivityMap& upperbounds() const
            {
                return mUpperbounds;
            }

            const BoundActivityMap& lowerbounds() const
            {
                return mLowerbounds;
            }

            unsigned& rPosition()
            {
                return mPosition;
            }

            const GiNaC::ex* pExpression() const
            {
                return mExpression;
            }

            const Bound* addUpperBound( Value* const );
            const Bound* addLowerBound( Value* const );
            unsigned setActive( const Bound*, bool );
            void deactivateBound( const Bound* );

            void print( std::ostream& = std::cout ) const;
            void printAllBounds( std::ostream& = std::cout ) const;
    };
}    // end namspace lra
#endif   /* _VARIABLE_H */
