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
//#define VS_USE_DEDUCTIONS

//#define VS_DELAY_BACKEND_CALL
#define VS_WITH_BACKEND

//#define VS_DEBUG
//#define VS_DEBUG_METHODS

#include "VSModule/Substitute.h"
#include "VSModule/State.h"
#include "../Module.h"
#include "../VariableBounds.h"

namespace smtrat
{
    class VSModule:
        public Module
    {
        private:

            /*
             * Type and object definitions:
             */
            struct unsignedIntPairCmp
            {
                bool operator ()( std::pair<unsigned, unsigned> n1, std::pair<unsigned, unsigned> n2 ) const
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

            typedef std::pair<std::pair<unsigned, unsigned>, vs::State*>                    ValStatePair;
            typedef std::map<std::pair<unsigned, unsigned>, vs::State*, unsignedIntPairCmp> ValuationMap;
            typedef std::pair<vs::Substitution, vs::StateVector>                            ChildrenGroup;
            typedef std::vector<ChildrenGroup>                                              ChildrenGroups;
            typedef std::map<const Constraint* const , vs::Condition*>                      ConstraintConditionMap;

            /*
             * Attributes:
             */
            bool                   debug;
            bool                   debugmethods;
            bool                   mInconsistentConstraintAdded;
            bool                   mFreshConstraintReceived;
            unsigned               mIDCounter;
            vs::State*             mpStateTree;
            ValuationMap*          mpRanking;
            ConstraintConditionMap mReceivedConstraintsAsConditions;
            GiNaC::symtab          mAllVariables;

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
            bool& rDebug()
            {
                return debug;
            }

            bool& rDebugMethods()
            {
                return debugmethods;
            }

            // Interfaces.
            bool assertSubformula( Formula::const_iterator );
            Answer isConsistent();
            void removeSubformula( Formula::const_iterator );

            // Printing methods.
            void printAll( std::ostream& = std::cout ) const;
            void printRanking( std::ostream& = std::cout ) const;
            void printRuntimes( std::ostream& = std::cout ) const;
            void printAnswer( std::ostream& = std::cout ) const;

        private:
            /*
             * Methods:
             */
            bool eliminate( vs::State*, const std::string&, vs::Condition* );
            bool substituteAll( vs::State*, vs::ConditionVector& );
            void propagateNewConditions( vs::State* );
            void increaseIDCounter();
            void insertDTinRanking( vs::State* );
            void insertDTsinRanking( vs::State* );
            bool eraseDTofRanking( vs::State& );
            void eraseDTsOfRanking( vs::State& );
            void updateInfeasibleSubset();
            void reset();
            #ifdef VS_USE_DEDUCTIONS
            void updateDeductions();
            std::vector<std::pair<std::string, GiNaC::numeric> > getNumericAssignment( const unsigned = 10 ) const;
            #endif
            std::vector<std::pair<std::string, std::pair<vs::Substitution_Type, GiNaC::ex> > > getSymbolicAssignment() const;
            static void allMinimumCoveringSets( const vs::ConditionSetSetSet&, vs::ConditionSetSet& );
            bool adaptPassedFormula( const vs::State& );
            Answer runBackendSolvers( vs::State* );
            vec_set_const_pFormula getOriginsOfCondition( const vs::Condition*, const vs::State* ) const;
            void checkAnswer() const;
    };

}    // end namespace smtrat

#endif   /** VSMODULE_H */
