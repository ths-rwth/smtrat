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
 * Class to create a substitution object.
 * @author Florian Corzilius
 * @since 2010-05-11
 * @version 2011-12-05
 */

#ifndef SMTRAT_VS_SUBSTITUTION_H
#define SMTRAT_VS_SUBSTITUTION_H

#include <ginac/flags.h>
#include "Condition.h"
#include "SqrtEx.h"

namespace vs
{
    /*
     *  Type and object definitions:
     */

    enum Substitution_Type { ST_NORMAL, ST_PLUS_EPSILON, ST_MINUS_INFINITY };

    class Substitution
    {
        private:

            /**
             * Members:
             */
            std::string*      mpVariable;
            GiNaC::ex*        mpVarAsEx;
            SqrtEx*           mpTerm;
            Substitution_Type mType;
            ConditionSet*     mpOriginalConditions;
            ConditionSet      mSideCondition;

        public:

            /**
             * Constructors:
             */
            Substitution( const std::string&, const GiNaC::ex&, const Substitution_Type&, const ConditionSet&, const ConditionSet& = ConditionSet() );
            Substitution( const std::string&, const GiNaC::ex&, const SqrtEx&, const Substitution_Type&, const ConditionSet&, const ConditionSet& = ConditionSet() );
            Substitution( const Substitution& );

            /**
             * Destructor:
             */
            ~Substitution();

            /**
             * Methods:
             */
            const std::string& variable() const
            {
                return *mpVariable;
            }
            const GiNaC::ex& varAsEx() const
            {
                return *mpVarAsEx;
            }

            const SqrtEx& term() const
            {
                return *mpTerm;
            }

            const GiNaC::symtab& termVariables() const
            {
                return mpTerm->variables();
            }

            Substitution_Type& rType()
            {
                return mType;
            }

            const Substitution_Type type() const
            {
                return mType;
            }

            ConditionSet& rOriginalConditions()
            {
                return *mpOriginalConditions;
            }

            const ConditionSet& originalConditions() const
            {
                return *mpOriginalConditions;
            }

            const ConditionSet& sideCondition() const
            {
                return mSideCondition;
            }

            ConditionSet& rSideCondition()
            {
                return mSideCondition;
            }

            // Data access methods (read only).
            unsigned valuate() const;

            // Operators.
            bool operator ==( const Substitution& ) const;
            bool operator <( const Substitution& ) const;
            friend std::ostream& operator <<( std::ostream&, const Substitution& );

            // Printing methods.
            void print( bool = false, bool = false, std::ostream& = std::cout, const std::string& = "" ) const;
            std::string toString( bool = false ) const;
        private:
            void getVariables( const GiNaC::ex&, GiNaC::symtab& );
    };

}    // end namspace vs

#endif
