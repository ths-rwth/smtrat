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
 * @file LRAOneModule.h
 * @author name surname <emailadress>
 *
 * @version 2012-04-05
 * Created on April 5th, 2012, 3:22 PM
 */

#ifndef LRAONEMODULE_H
#define LRAONEMODULE_H

#include "../Module.h"
#include "LRAOneModule/Value.h"
#include "LRAOneModule/Variable.h"
#include "LRAOneModule/Bound.h"
#include "LRAOneModule/Tableau.h"
#include <stdio.h>

namespace smtrat
{
    class LRAOneModule:
        public Module
    {
        public:
            struct exPointerComp
            {
                bool operator ()( const GiNaC::ex* const pExA, const GiNaC::ex* const pExB ) const
                {
                    return GiNaC::ex_is_less()( *pExA, *pExB );
                }
            };
            struct constraintPointerComp
            {
                bool operator ()( const Constraint* const pConstraintA, const Constraint* const pConstraintB ) const
                {
                    return (*pConstraintA) < (*pConstraintB);
                }
            };
            typedef std::map<const GiNaC::ex*, lraone::Variable*, exPointerComp>                                 ExVariableMap;
            typedef std::pair<const Constraint* const , std::vector<const lraone::Bound*> >                      ConstraintBoundPair;
            typedef std::map<const Constraint* const , std::vector<const lraone::Bound*>, constraintPointerComp> ConstraintBoundMap;
            typedef std::map<const Constraint*, const Formula* const, constraintPointerComp>                     ConstraintFormulaMap;
            typedef std::map<const lraone::Bound* const , const Constraint*>                                     BoundConstraintMap;

        private:

            /**
             * Members:
             */
            lraone::Tableau                mTableau;
            std::set<const Constraint*, constraintPointerComp > mLinearConstraints;
            std::set<const Constraint*, constraintPointerComp > mNonlinearConstraints;
            bool                           mInitialized;
            ExVariableMap                  mExistingVars;
            BoundConstraintMap             mBoundToConstraint;
            ConstraintFormulaMap           mConstraintToFormula;
            ConstraintBoundMap             mConstraintToBound;

        public:

            /**
             * Constructors:
             */
            LRAOneModule( Manager* const _tsManager, const Formula* const _formula );

            /**
             * Destructor:
             */
            virtual ~LRAOneModule();

            /**
             * Methods:
             */

            // Interfaces.
            bool inform( const Constraint* const );
            bool assertSubformula( Formula::const_iterator );
            void removeSubformula( Formula::const_iterator );
            Answer isConsistent();

        private:
            /**
             * Methods:
             */
            bool checkAssignmentForNonlinearConstraint() const;
            bool activateBound( lraone::Variable&, const lraone::Bound* );
            void setBound( lraone::Variable&, const Constraint_Relation&, bool, const GiNaC::numeric&, const Constraint* );
            const Formula* getSubformula( const lraone::Bound* ) const;
            void initialize();
    };

}    // namespace smtrat

#endif   /* LRAONEMODULE_H */
