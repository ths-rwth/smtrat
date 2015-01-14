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
 * Class to create a condition object.
 * @author Florian Corzilius
 * @since 2010-07-26
 * @version 2011-12-05
 */

#pragma once

#include <set>
#include "../../Common.h"

namespace vs
{
    /*
     * Type and object definitions:
     */

    class Condition
    {       
            // Members:
            static const double INFINITLY_MANY_SOLUTIONS_WEIGHT;

        private:

            mutable bool                   mFlag;
            mutable bool                   mRecentlyAdded;
            mutable size_t                 mValuation;
            const smtrat::ConstraintT*     mpConstraint;
            carl::PointerSet<Condition>*   mpOriginalConditions;
            

        public:

            // Constructors:
            Condition( const smtrat::ConstraintT*, size_t = 0, bool = false, const carl::PointerSet<Condition>& = carl::PointerSet<Condition>(), bool = false );
            Condition( const Condition& );

            // Destructor:
            ~Condition();

            // Methods:
            bool& rFlag() const
            {
                return mFlag;
            }

            bool flag() const
            {
                return mFlag;
            }

            bool& rRecentlyAdded() const
            {
                return mRecentlyAdded;
            }

            bool recentlyAdded() const
            {
                return mRecentlyAdded;
            }

            size_t& rValuation() const
            {
                return mValuation;
            }

            size_t valuation() const
            {
                return mValuation;
            }

            const smtrat::ConstraintT& constraint() const
            {
                return *mpConstraint;
            }

            const smtrat::ConstraintT* pConstraint() const
            {
                return mpConstraint;
            }

            carl::PointerSet<Condition>* pOriginalConditions() const
            {
                return mpOriginalConditions;
            }

            const carl::PointerSet<Condition>& originalConditions() const
            {
                return *mpOriginalConditions;
            }

            double valuate( const carl::Variable&, size_t, bool ) const;
            bool operator==( const Condition& ) const;
            bool operator<( const Condition& ) const;
            void print( std::ostream& = std::cout ) const;
    };

}    // end namspace vs
