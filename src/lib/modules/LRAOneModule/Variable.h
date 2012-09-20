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

    typedef std::set<const Bound*, boundComp> BoundSet;

    class Variable
    {
        private:

            /**
             * Members.
             */
            bool             mBasic;
            unsigned         mPosition;
            BoundSet         mUpperbounds;
            BoundSet         mLowerbounds;
            const Bound*     mpSupremum;
            const Bound*     mpInfimum;
            const GiNaC::ex* mExpression;
            Value            mAssignment;

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

            bool isBasic() const
            {
                return mBasic;
            }

            void setSupremum( const Bound* _supremum )
            {
                mpSupremum = _supremum;
            }

            const Bound* pSupremum() const
            {
                assert( !mpSupremum->origins().empty() );
                return mpSupremum;
            }

            const Bound& supremum() const
            {
                assert( !mpSupremum->origins().empty() );
                return *mpSupremum;
            }

            void setInfimum( const Bound* _infimum )
            {
                mpInfimum = _infimum;
            }

            const Bound* pInfimum() const
            {
                assert( !mpInfimum->origins().empty() );
                return mpInfimum;
            }

            const Bound& infimum() const
            {
                assert( !mpInfimum->origins().empty() );
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

            const BoundSet& upperbounds() const
            {
                return mUpperbounds;
            }

            const BoundSet& lowerbounds() const
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

            std::pair<const Bound*, std::pair<const Bound*, const Bound*> > addUpperBound( Value* const , const smtrat::Constraint* = NULL );
            std::pair<const Bound*, std::pair<const Bound*, const Bound*> > addLowerBound( Value* const , const smtrat::Constraint* = NULL );
            void deactivateBound( const Bound* );

            void print( std::ostream& = std::cout ) const;
            void printAllBounds( std::ostream& = std::cout, const std::string = "" ) const;
    };
}    // end namspace lra
#endif   /* _VARIABLE_H */
