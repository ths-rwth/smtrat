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
 * @file ILRAModule.h
 * @author name surname <emailadress>
 *
 * @version 2012-04-05
 * Created on April 5th, 2012, 3:22 PM
 */

#ifndef ILRAMODULE_H
#define ILRAMODULE_H

#define ILRA_USE_GINACRA

#include "../Module.h"
#include "TLRAModule/Value.h"
#include "TLRAModule/Variable.h"
#include "TLRAModule/Bound.h"
#include "TLRAModule/Tableau.h"
#include <stdio.h>
#ifdef ILRA_USE_GINACRA
#include <ginacra/ginacra.h>
#endif

#define ILRA_SIMPLE_CONFLICT_SEARCH
#define ILRA_REFINEMENT

namespace smtrat
{
    class ILRAModule:
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
            typedef std::map<const GiNaC::ex*, tlra::Variable<int>*, exPointerComp> ExVariableMap;
            typedef std::vector< std::vector< const tlra::Bound<int>* >* >          ConstraintBoundsMap;

        private:

            /**
             * Members:
             */
            bool                                  mInitialized;
            bool                                  mAssignmentFullfilsNonlinearConstraints;
            unsigned                              mMaxConstraintId;
            tlra::Tableau<int>                    mTableau;
            ConstraintSet                         mLinearConstraints;
            ConstraintSet                         mNonlinearConstraints;
            ExVariableMap                         mOriginalVars;
            ExVariableMap                         mSlackVars;
            ConstraintBoundsMap                   mConstraintToBound;
            std::vector<const tlra::Bound<int>* > mBoundCandidatesToPass;

        public:

            /**
             * Constructors:
             */
            ILRAModule( const Formula* const _formula, Manager* const _tsManager = NULL );

            /**
             * Destructor:
             */
            virtual ~ILRAModule();

            /**
             * Methods:
             */

            // Interfaces.
            bool inform( const Constraint* const );
            bool assertSubformula( Formula::const_iterator );
            void removeSubformula( Formula::const_iterator );
            Answer isConsistent();
            void updateModel();
            GiNaC::exmap getRationalModel() const;
            #ifdef ILRA_USE_GINACRA
            GiNaCRA::evalintervalmap getVariableBounds() const;
            #endif

        private:
            /**
             * Methods:
             */
            #ifdef ILRA_REFINEMENT
            void learnRefinements();
            #endif
            void adaptPassedFormula();
            bool checkAssignmentForNonlinearConstraint();
            bool activateBound( const tlra::Bound<int>*, std::set<const Formula*>& );
            void setBound( tlra::Variable<int>&, bool, const GiNaC::numeric&, const Constraint* );
            #ifdef ILRA_SIMPLE_CONFLICT_SEARCH
            void findSimpleConflicts( const tlra::Bound<int>& );
            #endif
            void initialize();
    };

}    // namespace smtrat

#endif   /* ILRAMODULE_H */
