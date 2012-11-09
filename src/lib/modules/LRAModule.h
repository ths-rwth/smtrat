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
 * @file LRAModule.h
 * @author name surname <emailadress>
 *
 * @version 2012-04-05
 * Created on April 5th, 2012, 3:22 PM
 */

#ifndef LRAMODULE_H
#define LRAMODULE_H

#define LRA_USE_GINACRA

#include "../Module.h"
#include "LRAModule/Value.h"
#include "LRAModule/Variable.h"
#include "LRAModule/Bound.h"
#include "LRAModule/Tableau.h"
#include <stdio.h>
#ifdef LRA_USE_GINACRA
#include <ginacra/ginacra.h>
#endif


#define LRA_SIMPLE_CONFLICT_SEARCH

namespace smtrat
{
    class LRAModule:
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
            typedef std::map<const GiNaC::ex*, lra::Variable*, exPointerComp>   ExVariableMap;
            typedef std::vector< std::vector< const lra::Bound* >* >            ConstraintBoundsMap;

        private:

            /**
             * Members:
             */
            bool                        mInitialized;
            bool                        mAssignmentFullfilsNonlinearConstraints;
            unsigned                    mMaxConstraintId;
            lra::Tableau                mTableau;
            ConstraintSet               mLinearConstraints;
            ConstraintSet               mNonlinearConstraints;
            ExVariableMap               mOriginalVars;
            ExVariableMap               mSlackVars;
            ConstraintBoundsMap         mConstraintToBound;
            std::vector<const lra::Bound* >  mBoundCandidatesToPass;

        public:

            /**
             * Constructors:
             */
            LRAModule( const Formula* const _formula, Manager* const _tsManager );

            /**
             * Destructor:
             */
            virtual ~LRAModule();

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
            #ifdef LRA_USE_GINACRA
            GiNaCRA::evalintervalmap getVariableBounds() const;
            #endif

        private:
            /**
             * Methods:
             */
            #ifdef LRA_REFINEMENT
            void learnRefinements();
            #endif
            void adaptPassedFormula();
            bool checkAssignmentForNonlinearConstraint();
            bool activateBound( const lra::Bound*, std::set<const Formula*>& );
            void setBound( lra::Variable&, bool, const GiNaC::numeric&, const Constraint* );
            #ifdef LRA_SIMPLE_CONFLICT_SEARCH
            void findSimpleConflicts( const lra::Bound& );
            #endif
            void initialize();
    };

}    // namespace smtrat

#endif   /* LRAMODULE_H */
