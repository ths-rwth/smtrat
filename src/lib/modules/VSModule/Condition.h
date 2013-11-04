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

#ifndef SMTRAT_VS_CONDITION_H
#define SMTRAT_VS_CONDITION_H

#include <set>
#include "../../Formula.h"

namespace vs
{
    /*
     * Type and object definitions:
     */

    class Condition
    {
        public:
            struct condPointerLess
            {
                bool operator ()( const Condition* const pCondA, const Condition* const pCondB ) const
                {
                    return (*pCondA).constraint() < (*pCondB).constraint();
                }
            };
            typedef std::set<const Condition*, condPointerLess> Set;

        private:

            // Members:
            mutable bool              mFlag;
            mutable bool              mRecentlyAdded;
            mutable unsigned          mValuation;
            const smtrat::Constraint* mpConstraint;
            Set*                      mpOriginalConditions;

        public:

            // Constructors:
            Condition( const smtrat::Constraint*, unsigned = 0, bool = false, const Set& = Set(), bool = false );
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

            const bool recentlyAdded() const
            {
                return mRecentlyAdded;
            }

            unsigned& rValuation() const
            {
                return mValuation;
            }

            unsigned valuation() const
            {
                return mValuation;
            }

            const smtrat::Constraint& constraint() const
            {
                return *mpConstraint;
            }

            const smtrat::Constraint* pConstraint() const
            {
                return mpConstraint;
            }

            Set* const pOriginalConditions() const
            {
                return mpOriginalConditions;
            }

            const Set& originalConditions() const
            {
                return *mpOriginalConditions;
            }

            double valuate( const carl::Variable&, unsigned, bool, bool ) const;
            bool operator ==( const Condition& ) const;
            bool operator <( const Condition& ) const;
            void print( std::ostream& = std::cout ) const;
    };

}    // end namspace vs

#endif
