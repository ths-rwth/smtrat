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
 * @file TLRAModule.h
 * @author name surname <emailadress>
 *
 * @version 2012-04-05
 * Created on April 5th, 2012, 3:22 PM
 */

#ifndef TLRAMODULE_H
#define TLRAMODULE_H

#include "../../Module.h"
#include "../../RuntimeSettings.h"
#include "Numeric.h"
#include "../LRAModule/Value.hpp"
#include "../LRAModule/Variable.hpp"
#include "../LRAModule/Bound.hpp"
#include "../LRAModule/Tableau.hpp"
#include <stdio.h>


#define TLRA_SIMPLE_CONFLICT_SEARCH

namespace smtrat
{
    class TLRAModule:
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
            typedef std::map<const GiNaC::ex*, tlra::Variable<tlra::Numeric>*, exPointerComp>   ExVariableMap;
            typedef std::vector< std::vector< const tlra::Bound<tlra::Numeric>* >* >            ConstraintBoundsMap;

        private:

            /**
             * Members:
             */
            bool                        mInitialized;
            bool                        mAssignmentFullfilsNonlinearConstraints;
            unsigned                    mNumberOfReceivedLinearNeqConstraints;
            tlra::Tableau<tlra::Numeric>  mTableau;
            ConstraintSet               mLinearConstraints;
            ConstraintSet               mNonlinearConstraints;
            ExVariableMap               mOriginalVars;
            ExVariableMap               mSlackVars;
            ConstraintBoundsMap         mConstraintToBound;
            std::vector<const tlra::Bound<tlra::Numeric>* >  mBoundCandidatesToPass;

        public:

            /**
             * Constructors:
             */
            TLRAModule( ModuleType _type, const Formula* const, RuntimeSettings*, Answer&, Manager* const = NULL );

            /**
             * Destructor:
             */
            virtual ~TLRAModule();

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
            GiNaCRA::evalintervalmap getVariableBounds() const;
            void initialize();

        private:
            /**
             * Methods:
             */
            #ifdef TLRA_REFINEMENT
            void learnRefinements();
            #endif
            void adaptPassedFormula();
            bool checkAssignmentForNonlinearConstraint();
            bool activateBound( const tlra::Bound<tlra::Numeric>*, std::set<const Formula*>& );
            void setBound( tlra::Variable<tlra::Numeric>&, bool, const tlra::Numeric&, const Constraint* );
            #ifdef TLRA_SIMPLE_CONFLICT_SEARCH
            void findSimpleConflicts( const tlra::Bound<tlra::Numeric>& );
            #endif
            void initialize( const Constraint* const );
    };

}    // namespace smtrat

#endif   /* LRAMODULE_H */
