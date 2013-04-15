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
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2012-04-05
 * Created on April 5th, 2012, 3:22 PM
 */

#ifndef TLRAMODULE_H
#define TLRAMODULE_H

#include "../../Module.h"
#include "../../RuntimeSettings.h"
#include "Numeric.h"
#include "Value.hpp"
#include "Variable.hpp"
#include "Bound.hpp"
#include "Tableau.hpp"
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
            struct Context
            {
                const smtrat::Formula* origin;
                smtrat::Formula::iterator position;
            };
            typedef std::map< const GiNaC::ex*, tlra::Variable<tlra::Numeric>*, exPointerComp>              ExVariableMap;
            typedef std::map< const Constraint*, std::vector< const tlra::Bound<tlra::Numeric>* >*, constraintPointerComp > ConstraintBoundsMap;
            typedef std::map< const Constraint*, Context, constraintPointerComp >                           ConstraintContextMap;
            typedef std::map< const tlra::Bound<tlra::Numeric>*, const Constraint* >                                        BoundConstraintMap;

        private:

            /**
             * Members:
             */
            bool                         mInitialized;
            bool                         mAssignmentFullfilsNonlinearConstraints;
            tlra::Tableau<tlra::Numeric> mTableau;
            ConstraintSet                mLinearConstraints;
            ConstraintSet                mNonlinearConstraints;
            ConstraintContextMap         mActiveResolvedNEQConstraints;
            ConstraintContextMap         mActiveUnresolvedNEQConstraints;
            ConstraintSet                mResolvedNEQConstraints;
            ExVariableMap                mOriginalVars;
            ExVariableMap                mSlackVars;
            ConstraintBoundsMap          mConstraintToBound;
            BoundConstraintMap           mBoundToUnequalConstraintMap;
            std::vector<const tlra::Bound<tlra::Numeric>* >  mBoundCandidatesToPass;

        public:

            /**
             * Constructors:
             */
            TLRAModule( ModuleType _type, const Formula* const, RuntimeSettings*, Conditionals&, Manager* const = NULL );

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

            void printLinearConstraints ( std::ostream& = std::cout, const std::string = "" ) const;
            void printNonlinearConstraints ( std::ostream& = std::cout, const std::string = "" ) const;
            void printOriginalVars ( std::ostream& = std::cout, const std::string = "" ) const;
            void printSlackVars ( std::ostream& = std::cout, const std::string = "" ) const;
            void printConstraintToBound ( std::ostream& = std::cout, const std::string = "" ) const;
            void printBoundCandidatesToPass ( std::ostream& = std::cout, const std::string = "" ) const;
            void printRationalModel ( std::ostream& = std::cout, const std::string = "" ) const;


            void printTableau ( std::ostream& _out = std::cout, const std::string _init = "" ) const
            {
                mTableau.print( _out, 28, _init );
            }

            const ExVariableMap& slackVariables() const
            {
                return mSlackVars;
            }

            const tlra::Variable<tlra::Numeric>* const getSlackVariable( const Constraint* const _constraint ) const
            {
                ConstraintBoundsMap::const_iterator iter = mConstraintToBound.find( _constraint );
                assert( iter != mConstraintToBound.end() );
                return iter->second->back()->pVariable();
            }


        private:
            /**
             * Methods:
             */
            #ifdef TLRA_REFINEMENT
            void learnRefinements();
            #endif
            void adaptPassedFormula();
            bool checkAssignmentForNonlinearConstraint();
            void splitUnequalConstraint( const Constraint* );
            bool activateBound( const tlra::Bound<tlra::Numeric>*, std::set<const Formula*>& );
            void setBound( tlra::Variable<tlra::Numeric>&, bool, const tlra::Numeric&, const Constraint* );
            #ifdef TLRA_SIMPLE_CONFLICT_SEARCH
            void findSimpleConflicts( const tlra::Bound<tlra::Numeric>& );
            #endif
            void initialize( const Constraint* const );
    };

}    // namespace smtrat

#endif   /* LRAMODULE_H */
