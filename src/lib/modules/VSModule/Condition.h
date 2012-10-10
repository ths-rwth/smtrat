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

#define VS_ELIMINATE_MULTI_ROOTS

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

            /*
             * Intern type structur:
             */
            struct condComp
            {
                bool operator ()( const Condition* const pCondA, const Condition* const pCondB ) const
                {
                    return (*pCondA).constraint() < (*pCondB).constraint();
                }
            };
            typedef std::set<Condition*, condComp> ConditionSet;

        private:

            /**
             * Members:
             */
            bool                mFlag;
            bool                mRecentlyAdded;
            unsigned            mValuation;
            const smtrat::Constraint* mpConstraint;
            ConditionSet*       mpOriginalConditions;

        public:

            /**
             * Constructors:
             */

            Condition();

            Condition( const smtrat::Constraint* );

            Condition( const smtrat::Constraint*, unsigned );

            Condition( const smtrat::Constraint*, const bool, const ConditionSet&, const unsigned );

            Condition( const smtrat::Constraint*, const bool, const ConditionSet&, const unsigned, const bool );

            Condition( const Condition& );

            /**
             * Destructor:
             */
            ~Condition();

            /**
             * Methods:
             */

            bool& rFlag()
            {
                return mFlag;
            }

            const bool flag() const
            {
                return mFlag;
            }

            bool& rRecentlyAdded()
            {
                return mRecentlyAdded;
            }

            const bool recentlyAdded() const
            {
                return mRecentlyAdded;
            }

            unsigned& rValuation()
            {
                return mValuation;
            }

            const unsigned valuation() const
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

            ConditionSet& rOriginalConditions()
            {
                return *mpOriginalConditions;
            }

            const ConditionSet& originalConditions() const
            {
                return *mpOriginalConditions;
            }

            void changeRelationTo( smtrat::Constraint_Relation _relation )
            {
                mpConstraint = smtrat::Formula::newConstraint( mpConstraint->lhs(), _relation );
            }

            unsigned valuate( const std::string, const unsigned, const bool );
            bool bestVariable( std::string& ) const;
            unsigned bestVariable2( std::string& ) const;
            bool operator ==( const Condition& ) const;
            bool operator <( const Condition& ) const;
            void print( std::ostream& ) const;
    };

    typedef std::set<Condition*, Condition::condComp> ConditionSet;

}    // end namspace vs

#endif
