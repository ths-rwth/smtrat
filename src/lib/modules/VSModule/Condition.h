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

//#define VS_ELIMINATE_MULTI_ROOTS

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
            struct Info
            {
                bool flag;
                bool recentlyAdded;
                unsigned valuation;
            };
            struct condComp
            {
                bool operator ()( const Condition* const pCondA, const Condition* const pCondB ) const
                {
                    return (*pCondA->pConstraint()->load()) < (*pCondB->pConstraint()->load());
                }
            };
            typedef std::set<const Condition*, condComp> ConditionSet;

        private:

            /**
             * Members:
             */
            Info*           mpInfo;
            Constraint_Atom mpConstraint;
            ConditionSet*   mpOriginalConditions;

        public:

            /**
             * Constructors:
             */

            Condition();

            Condition( Constraint_Atom );

            Condition( Constraint_Atom, unsigned );

            Condition( Constraint_Atom, bool, const ConditionSet&, unsigned );

            Condition( Constraint_Atom, bool, const ConditionSet&, unsigned, bool );

            Condition( const Condition& );

            /**
             * Destructor:
             */
            ~Condition();

            /**
             * Methods:
             */

            bool& rFlag() const
            {
                return mpInfo->flag;
            }

            bool flag() const
            {
                return mpInfo->flag;
            }

            bool& rRecentlyAdded() const
            {
                return mpInfo->recentlyAdded;
            }

            const bool recentlyAdded() const
            {
                return mpInfo->recentlyAdded;
            }

            unsigned& rValuation() const
            {
                return mpInfo->valuation;
            }

            unsigned valuation() const
            {
                return mpInfo->valuation;
            }

            Constraint_Atom pConstraint() const
            {
                return mpConstraint;
            }

            ConditionSet* const pOriginalConditions() const
            {
                return mpOriginalConditions;
            }

            const ConditionSet& originalConditions() const
            {
                return *mpOriginalConditions;
            }

            double valuate( const std::string&, unsigned, bool ) const;
            bool bestVariable( std::string& ) const;
            unsigned bestVariable2( std::string& ) const;
            bool operator ==( const Condition& ) const;
            bool operator <( const Condition& ) const;
            void print( std::ostream& = std::cout ) const;
    };

    typedef std::set<const Condition*, Condition::condComp> ConditionSet;

}    // end namspace vs

#endif
