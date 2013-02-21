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
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2013-02-07
 * Created on April 5th, 2012, 3:22 PM
 */

#ifndef LRAMODULE_H
#define LRAMODULE_H

#define LRA_USE_GINACRA

#include "../../Module.h"
#include "../../RuntimeSettings.h"
#include "Value.h"
#include "Variable.h"
#include "Bound.h"
#include "Tableau.h"
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
            struct Context
            {
                const smtrat::Formula* origin;
                smtrat::Formula::iterator position;
            };
            typedef std::map< const GiNaC::ex*, lra::Variable*, exPointerComp>                              ExVariableMap;
            typedef std::map< const Constraint*, std::vector< const lra::Bound* >*, constraintPointerComp > ConstraintBoundsMap;
            typedef std::map< const Constraint*, Context, constraintPointerComp >                           ConstraintContextMap;
            typedef std::map< const lra::Bound*, const Constraint* >                                        BoundConstraintMap;

        private:

            /**
             * Members:
             */
            bool                            mInitialized;
            bool                            mAssignmentFullfilsNonlinearConstraints;
            lra::Tableau                    mTableau;
            ConstraintSet                   mLinearConstraints;
            ConstraintSet                   mNonlinearConstraints;
            ConstraintContextMap            mActiveResolvedNEQConstraints;
            ConstraintContextMap            mActiveUnresolvedNEQConstraints;
            ConstraintSet                   mResolvedNEQConstraints;
            ExVariableMap                   mOriginalVars;
            ExVariableMap                   mSlackVars;
            ConstraintBoundsMap             mConstraintToBound;
            BoundConstraintMap              mBoundToUnequalConstraintMap;
            std::vector<const lra::Bound* > mBoundCandidatesToPass;

        public:

            /**
             * Constructors:
             */
            LRAModule( ModuleType _type, const Formula* const, RuntimeSettings*, bool&, Manager* const = NULL );

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

            const lra::Variable* const getSlackVariable( const Constraint* const _constraint ) const
            {
                ConstraintBoundsMap::const_iterator iter = mConstraintToBound.find( _constraint );
                assert( iter != mConstraintToBound.end() );
                return iter->second->back()->pVariable();
            }

        private:
            /**
             * Methods:
             */
            #ifdef LRA_REFINEMENT
            void learnRefinements();
            #endif
            void adaptPassedFormula();
            bool checkAssignmentForNonlinearConstraint();
            void splitUnequalConstraint( const Constraint* );
            bool activateBound( const lra::Bound*, std::set<const Formula*>& );
            void setBound( lra::Variable&, bool, const GiNaC::numeric&, const Constraint* );
            #ifdef LRA_SIMPLE_CONFLICT_SEARCH
            void findSimpleConflicts( const lra::Bound& );
            #endif
            void initialize( const Constraint* const );
    };

}    // namespace smtrat

#endif   /* LRAMODULE_H */
