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
 * @version 2012-04-05
 * Created on April 5th, 2012, 3:22 PM
 */

#ifndef LRAMODULE_H
#define LRAMODULE_H


#include "../../Module.h"
#include "../../RuntimeSettings.h"
#include "../../datastructures/lra/Value.hpp"
#include "../../datastructures/lra/Variable.hpp"
#include "../../datastructures/lra/Bound.hpp"
#include "../../datastructures/lra/Tableau.hpp"
#include "LRAModuleStatistics.h"
#include <stdio.h>

namespace smtrat
{
    typedef carl::Numeric<Rational>                   LRABoundType;
    typedef carl::Numeric<Rational>                   LRAEntryType;
    typedef lra::Bound<LRABoundType, LRAEntryType>    LRABound;
    typedef lra::Variable<LRABoundType, LRAEntryType> LRAVariable;
    typedef lra::Value<LRABoundType>                  LRAValue;
    typedef lra::Tableau<LRABoundType, LRAEntryType>  LRATableau;
    
    class LRAModule:
        public Module
    {
        public:
            struct Context
            {
                const Formula*                      origin;
                std::list<const Formula*>::iterator position;
            };
            typedef std::map< carl::Variable, LRAVariable*>                   VarVariableMap;
            typedef FastPointerMap<Polynomial, LRAVariable*>                  ExVariableMap;
            typedef FastPointerMap<Constraint, std::vector<const LRABound*>*> ConstraintBoundsMap;
            typedef FastPointerMap<Constraint, Context>                       ConstraintContextMap;

        private:

            /**
             * Members:
             */
            bool                       mInitialized;
            bool                       mAssignmentFullfilsNonlinearConstraints;
            LRATableau mTableau;
            PointerSet<Constraint>     mLinearConstraints;
            PointerSet<Constraint>     mNonlinearConstraints;
            ConstraintContextMap       mActiveResolvedNEQConstraints;
            ConstraintContextMap       mActiveUnresolvedNEQConstraints;
            PointerSet<Constraint>     mResolvedNEQConstraints;
            ConstraintBoundsMap        mConstraintToBound;
            carl::Variable             mDelta;
            std::vector<const LRABound* >  mBoundCandidatesToPass;
            #ifdef SMTRAT_DEVOPTION_Statistics
            ///
            LRAModuleStatistics* mpStatistics;
            #endif

        public:

            /**
             * Constructors:
             */
            LRAModule( ModuleType _type, const Input*, RuntimeSettings*, Conditionals&, Manager* const = NULL );

            /**
             * Destructor:
             */
            virtual ~LRAModule();

            /**
             * Methods:
             */

            // Interfaces.
            bool inform( const Constraint* const );
            void init();
            bool assertSubformula( Input::const_iterator );
            void removeSubformula( Input::const_iterator );
            Answer isConsistent();
            void updateModel() const;
            EvalRationalMap getRationalModel() const;
            EvalIntervalMap getVariableBounds() const;

            void printLinearConstraints ( std::ostream& = std::cout, const std::string = "" ) const;
            void printNonlinearConstraints ( std::ostream& = std::cout, const std::string = "" ) const;
            void printConstraintToBound ( std::ostream& = std::cout, const std::string = "" ) const;
            void printBoundCandidatesToPass ( std::ostream& = std::cout, const std::string = "" ) const;
            void printRationalModel ( std::ostream& = std::cout, const std::string = "" ) const;

            const VarVariableMap& originalVariables() const
            {
                return mTableau.originalVars();
            }
            
            const ExVariableMap& slackVariables() const
            {
                return mTableau.slackVars();
            }

            const LRAVariable* getSlackVariable( const Constraint* _constraint ) const
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
            bool activateBound( const LRABound*, const PointerSet<Formula>& );
            void setBound( const Constraint* );
            void addSimpleBoundDeduction( const LRABound*, bool = false );
            void addSimpleBoundConflict( const LRABound&, const LRABound&, bool = false );
            void findSimpleConflicts( const LRABound& );
            bool gomory_cut();
            bool cuts_from_proofs();
            bool branch_and_bound();
            bool assignmentConsistentWithTableau( const EvalRationalMap&, const LRABoundType& ) const;
            bool assignmentCorrect() const;
    };

}    // namespace smtrat

#endif   /* LRAMODULE_H */
