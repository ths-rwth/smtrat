/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2013 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT. If not, see <http://www.gnu.org/licenses/>.
 *
 */

/**
 * @file Manager.h
 *
 * @author  Florian Corzilius
 * @author  Ulrich Loup
 * @author  Sebastian Junges
 * @author  Henrik Schmitz
 * @since   2012-01-18
 * @version 2013-01-11
 */

#ifndef SMTRAT_MANAGER_H
#define SMTRAT_MANAGER_H

#include <vector>

#include "Answer.h"
#include "ModuleFactory.h"
#include "StrategyGraph.h"
#include "modules/ModuleType.h"
#include "Module.h"
#include "config.h"
#include "modules/StandardModuleFactory.h"

namespace smtrat
{
    // Forward declaration to speed up compile-time.
    class Constraint;
    /**
     * Base class for solvers. This is the interface to the user.
     */
    class Manager
    {
        friend class Module;
        private:

            /// a vector of flags, which indicate that an answer has been found of an antecessor module of the primary module
            std::vector< std::atomic_bool* > mPrimaryBackendFoundAnswer;
            /// the constraints so far passed to the primary backend
            Formula* mpPassedFormula;
            /// the backtrack points
            std::vector< Formula::iterator > mBacktrackPoints;
            /// all generated instances of modules
            std::vector<Module*> mGeneratedModules;
            /// a mapping of each module to its backends
            std::map<const Module* const, std::vector<Module*> > mBackendsOfModules;
            /// the primary backends
            Module* mpPrimaryBackend;
            /// a Boolean showing whether the manager has received new constraint after the last consistency check
            bool mBackendsUptodate;
            /// modules we can use
            std::map<const ModuleType, ModuleFactory*>* mpModuleFactories;
            /// primary strategy
            StrategyGraph mStrategyGraph;
            /// channel to write debug output
            std::ostream mDebugOutputChannel;
            #ifdef SMTRAT_STRAT_PARALLEL_MODE
            /// contains all threads to assign jobs to
            ThreadPool* mpThreadPool;
            /// the number of branches occurring in the strategy (the same as the number of leaves)
            unsigned mNumberOfBranches;
            /// the number of cores of the system we run on
            unsigned mNumberOfCores;
            /// a flag indicating whether we might run in parallel eventually
            bool mRunsParallel;
            /// a mutex for exclusive access of the backends to members of this state
            mutable std::mutex mBackendsMutex;

            void initialize();
            #endif

        public:
            Manager();
            ~Manager();

            // Main interfaces
            bool inform( const Constraint* const _constraint )
            {
                return mpPrimaryBackend->inform( _constraint );
            }

            bool add( Formula* _subformula )
            {
                mpPassedFormula->addSubformula( _subformula );
                auto pos = mpPassedFormula->last();
                auto btp = mBacktrackPoints.end();
                while( btp != mBacktrackPoints.begin() )
                {
                    --btp;
                    if( *btp == mpPassedFormula->end() )
                    {
                        *btp = pos;
                    }
                    else
                    {
                        break;
                    }
                }
                return mpPrimaryBackend->assertSubformula( pos );
            }

            Answer check()
            {
                #ifdef SMTRAT_STRAT_PARALLEL_MODE
                initialize();
                #endif
                #ifdef SMTRAT_DEVOPTION_MeasureTime
                mpPrimaryBackend->startCheckTimer();
                #endif
                *mPrimaryBackendFoundAnswer.back() = false;
                mpPassedFormula->getPropositions();
                return mpPrimaryBackend->isConsistent();
            }

            Formula::iterator remove( Formula::iterator _subformula )
            {
                assert( _subformula != mpPassedFormula->end() );
                mpPrimaryBackend->removeSubformula( _subformula );
                return mpPassedFormula->erase( _subformula );
            }
            
            void push()
            {
                mBacktrackPoints.push_back( mpPassedFormula->end() );
            }
            
            bool pop()
            {
                if( mBacktrackPoints.empty() ) return false;
                auto subFormula = mBacktrackPoints.back();
                while( subFormula != mpPassedFormula->end() )
                {
                    subFormula = remove( subFormula );
                }
                mBacktrackPoints.pop_back();
                return true;
            }
            
            const vec_set_const_pFormula& infeasibleSubsets() const
            {
                return mpPrimaryBackend->infeasibleSubsets();
            }

            const Module::Model model() const
            {
                mpPrimaryBackend->updateModel();
                return mpPrimaryBackend->model();
            }

            const Formula& formula() const
            {
                return *mpPassedFormula;
            }
            
            void printAssignment( std::ostream& ) const;
            void printValue( const std::string&, std::ostream& ) const;
            void printAssertions( std::ostream& ) const;
            void printInfeasibleSubset( std::ostream& ) const;
            
            // Internally used interfaces
            void addModuleType( const ModuleType _moduleType, ModuleFactory* _factory )
            {
                mpModuleFactories->insert( std::pair<const ModuleType, ModuleFactory*>( _moduleType, _factory ) );
            }

            const std::vector<Module*>& getAllGeneratedModules() const
            {
                return mGeneratedModules;
            }
            
            const std::map<const ModuleType, ModuleFactory*>& rModuleFactories() const
            {
                return *mpModuleFactories;
            }
            
            std::ostream& rDebugOutputChannel()
            {
                return mDebugOutputChannel;
            }
            
        protected:

            StrategyGraph& rStrategyGraph()
            {
                return mStrategyGraph;
            }

            std::vector<Module*> getAllBackends( Module* _module ) const
            {
                // Mutex?
                auto iter = mBackendsOfModules.find( _module );
                assert( iter != mBackendsOfModules.end() );
                std::vector<Module*> result = iter->second;
                return result;
            }
            
            unsigned addBackendIntoStrategyGraph( unsigned _at, ModuleType _moduleType, ConditionEvaluation _conditionEvaluation = isCondition )
            {
                return mStrategyGraph.addBackend( _at, _moduleType, _conditionEvaluation );
            }

            void addBacklinkIntoStrategyGraph( unsigned _from, unsigned _to, ConditionEvaluation _conditionEvaluation = isCondition )
            {
                mStrategyGraph.addBacklink( _from, _to, _conditionEvaluation );
            }

            #ifdef SMTRAT_STRAT_PARALLEL_MODE
            const bool runsParallel() const
            {
                return mRunsParallel;
            }
            #endif

            std::vector<Module*> getBackends( Formula*, Module*, std::atomic_bool* );
            #ifdef SMTRAT_STRAT_PARALLEL_MODE
            std::future<Answer> submitBackend( Module* );
            void checkBackendPriority( Module* );
            #endif
    };
}    // namespace smtrat
#endif   /** SMTRAT_MANAGER_H */
