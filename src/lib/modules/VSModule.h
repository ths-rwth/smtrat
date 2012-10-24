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
 * @file VSModule.h
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * Created on January 18, 2012, 3:45 PM
 */

#ifndef SMTRAT_VSMODULE_H
#define SMTRAT_VSMODULE_H

#define VS_INCREMENTAL
//#define VS_BACKTRACKING
#define VS_INFEASIBLE_SUBSET_GENERATION

#define VS_DELAY_BACKEND_CALL
#define VS_WITH_BACKEND

//#define VS_DEBUG
#define VS_STATISTICS
//#define VS_PRINT_ANSWERS
//#define VS_LOG_INTERMEDIATE_STEPS_OF_ASSIGNMENT
//#define VS_LOG_INFSUBSETS_OF_BACKEND

#include "VSModule/Substitute.h"
#include "VSModule/State.h"
#include "../Module.h"

namespace smtrat
{
    class VSModule:
        public Module
    {
        private:

            /*
             * Type and object definitions:
             */
            typedef std::pair<unsigned, unsigned> UnsignedPair;
            struct unsignedPairCmp
            {
                bool operator ()( UnsignedPair n1, UnsignedPair n2 ) const
                {
                    if( n1.first > n2.first )
                    {
                        return true;
                    }
                    else if( n1.first == n2.first && n1.second > n2.second )
                    {
                        return true;
                    }
                    else
                    {
                        return false;
                    }
                }
            };

            typedef std::pair<UnsignedPair, vs::State*>                 ValStatePair;
            typedef std::map<UnsignedPair, vs::State*, unsignedPairCmp> ValuationMap;
            typedef std::map<const Constraint* const , vs::Condition*>  ConstraintConditionMap;

            /*
             * Attributes:
             */
            bool                   mFreshConstraintReceived;
            bool                   mInconsistentConstraintAdded;
            unsigned               mIDCounter;
            #ifdef VS_STATISTICS
            unsigned               mStepCounter;
            #endif
            vs::State*             mpStateTree;
            GiNaC::symtab          mAllVariables;
            ConstraintConditionMap mConstraintConditionMap;
            ValuationMap           mRanking;

        public:

            /*
             * Constructors:
             */
            VSModule( Manager* const _tsManager, const Formula* const );

            /*
             * Destructor:
             */
            ~VSModule();

            /*
             * Methods:
             */
            // Interfaces.
            bool assertSubformula( Formula::const_iterator );
            Answer isConsistent();
            void removeSubformula( Formula::const_iterator );

            // Printing methods.
            void printAll( std::ostream& = std::cout ) const;
            void printRanking( std::ostream& = std::cout ) const;
            void printAnswer( std::ostream& = std::cout ) const;

        private:

            /*
             * Some more type definitions.
             */
            typedef std::pair<vs::Substitution, vs::StateVector> ChildrenGroup;
            typedef std::vector<ChildrenGroup>                   ChildrenGroups;

            /*
             * Methods:
             */
            bool eliminate( vs::State*, const std::string&, const vs::Condition* );
            bool substituteAll( vs::State*, vs::ConditionVector& );
            void propagateNewConditions( vs::State* );
            void increaseIDCounter();
            void insertDTinRanking( vs::State* );
            void insertDTsinRanking( vs::State* );
            bool eraseDTofRanking( vs::State& );
            void eraseDTsOfRanking( vs::State& );
            void updateInfeasibleSubset();
            void reset();
            std::vector<std::pair<std::string, std::pair<vs::Substitution_Type, GiNaC::ex> > > getSymbolicAssignment() const;
            static void allMinimumCoveringSets( const vs::ConditionSetSetSet&, vs::ConditionSetSet& );
            bool adaptPassedFormula( const vs::State& );
            Answer runBackendSolvers( vs::State* );
            #ifdef VS_LOG_INTERMEDIATE_STEPS_OF_ASSIGNMENT
            void checkAnswer() const;
            #endif
    };

}    // end namespace smtrat

#endif   /** VSMODULE_H */
