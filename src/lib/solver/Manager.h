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

#include "ModuleFactory.h"
#include "StrategyGraph.h"
#include "../modules/ModuleType.h"
#include "Module.h"
#include "../config.h"
#include "../modules/StandardModuleFactory.h"
#include "GeneralStatistics.h"
#include "QuantifierManager.h"

namespace smtrat
{
    // Forward declaration to speed up compile-time.
    class Constraint;
    
    /**
     * Base class for solvers. This is the interface to the user.
     **/
    class Manager
    {
        friend class Module;
        private:

            /// a vector of flags, which indicate that an answer has been found of an antecessor module of the primary module
            std::vector< std::atomic_bool* > mPrimaryBackendFoundAnswer;
            /// the constraints so far passed to the primary backend
            ModuleInput* mpPassedFormula;
            /// The propositions of the passed formula.
            Condition mPropositions;
            /// the backtrack points
            std::vector< std::list<const Formula*>::iterator > mBacktrackPoints;
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
			/// quantified variables
			QuantifierManager mQuantifierManager;
            /// the logic this solver considers
            Logic mLogic;
            #ifdef SMTRAT_DEVOPTION_Statistics
            /// Stores all statistics for the solver this manager belongs to.
            GeneralStatistics* mpStatistics;
            #endif
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

            /**
             * Initializes some members of the manager, which are only needed for supporting parallel module calls.
             */
            void initialize();
            #endif

        public:
            /**
             * Constructs a manager.
             */
            Manager();
            
            /**
             * Destructs a manager.
             */
            ~Manager();

            // Main interfaces
            
            /**
             * Informs the solver about a constraint. Optimally, it should be informed about all constraints,
             * which it will receive eventually, before any of them is added as part of a formula with the 
             * interface add(..).
             * @param _constraint The constraint to inform about.
             * @return false, if it is easy to decide (for any module used of this solver), whether 
             *          the constraint itself is inconsistent;
             *          true, otherwise.
             */
            bool inform( const Formula* _constraint )
            {
                return mpPrimaryBackend->inform( _constraint );
            }

            /**
             * Adds the given formula to the conjunction of formulas, which will be considered for the next 
             * satisfiability check.
             * @param _subformula The formula to add.
             * @return false, if it is easy to decide whether adding this formula creates a conflict;
             *          true, otherwise.
             */
            bool add( const Formula* _subformula )
            {
                mpPassedFormula->push_back( _subformula );
                auto pos = --(mpPassedFormula->end());
                auto btp = mBacktrackPoints.end();
                while( btp != mBacktrackPoints.begin() )
                {
                    --btp;
                    if( *btp == mpPassedFormula->end() )
                        *btp = pos;
                    else
                        break;
                }
                return mpPrimaryBackend->assertSubformula( pos );
            }

            /**
             * Checks the so far added formulas for satisfiability.
             * @return True, if the conjunction of the so far added formulas is satisfiable;
             *          False, if it not satisfiable;
             *          Unknown, if this solver cannot decide whether it is satisfiable or not.
             */
            Answer check()
            {
                #ifdef SMTRAT_STRAT_PARALLEL_MODE
                initialize();
                #endif
                *mPrimaryBackendFoundAnswer.back() = false;
                mpPassedFormula->updateProperties();
                return mpPrimaryBackend->isConsistent();
            }

            /**
             * Removes the formula at the given position in the conjunction of formulas,
             * which will be considered for the next satisfiability check.
             * @param _subformula The position of the formula to remove.
             * @return An iterator to the formula after the position of the just removed
             *          formula. If the removed formula has been the last element, the 
             *          end of the conjunction of formulas, which will be considered for the 
             *          next satisfiability check is returned.
             */
            std::list<const Formula*>::iterator remove( std::list<const Formula*>::iterator _subformula )
            {
                assert( _subformula != mpPassedFormula->end() );
                mpPrimaryBackend->removeSubformula( _subformula );
                return mpPassedFormula->erase( _subformula );
            }
            
            /**
             * Pushes a backtrack point to the stack of backtrack points.
             * 
             * Note, that this interface has not necessarily be used to apply a solver constructed
             * with SMT-RAT, but is often required by state-of-the-art SMT solvers when embedding
             * a theory solver constructed with SMT-RAT into them.
             */
            void push()
            {
                mBacktrackPoints.push_back( mpPassedFormula->end() );
            }
            
            /**
             * Pops a backtrack point from the stack of backtrack points. This provokes, that
             * all formulas which have been added after that backtrack point are removed.
             * 
             * Note, that this interface has not necessarily be used to apply a solver constructed
             * with SMT-RAT, but is often required by state-of-the-art SMT solvers when embedding
             * a theory solver constructed with SMT-RAT into them.
             */
            bool pop()
            {
                if( mBacktrackPoints.empty() ) return false;
                auto subFormula = mBacktrackPoints.back();
                while( subFormula != mpPassedFormula->end() )
                    subFormula = remove( subFormula );
                mBacktrackPoints.pop_back();
                return true;
            }
            
            /**
             * @return All infeasible subsets of the set so far added formulas.
             * 
             * Note, that the conjunction of the so far added formulas must be inconsistent to
             * receive an infeasible subset.
             */
            const vec_set_const_pFormula& infeasibleSubsets() const
            {
                return mpPrimaryBackend->infeasibleSubsets();
            }

            /**
             * Determines variables assigned by the currently found satisfying assignment to an equal value in their domain.
             * @return A list of vectors of variables, stating that the variables in one vector are assigned to equal values.
             */
			std::list<std::vector<carl::Variable>> getModelEqualities() const
			{
				return mpPrimaryBackend->getModelEqualities();
			}

            /**
             * @return An assignment of the variables, which occur in the so far added
             *          formulas, to values of their domains, such that it satisfies the 
             *          conjunction of these formulas.
             * 
             * Note, that an assignment is only provided if the conjunction of so far added
             * formulas is satisfiable. Furthermore, when solving non-linear real arithmetic 
             * formulas the assignment could contain other variables or freshly introduced
             * variables.
             */
            const Model model() const
            {
                mpPrimaryBackend->updateModel();
                return mpPrimaryBackend->model();
            }

            /**
             * @return The conjunction of so far added formulas.
             */
            const std::list<const Formula*>& formula() const
            {
                return *mpPassedFormula;
            }
            
            /**
             * Prints the currently found assignment of variables occurring in the so far 
             * added formulas to values of their domains, if the conjunction of these 
             * formulas is satisfiable.
             * @param The stream to print on.
             */
            void printAssignment( std::ostream& _out ) const
            {
                mpPrimaryBackend->printModel( _out );
            }
    
            /**
             * Prints the so far added formulas.
             * @param _out The stream to print on.
             */
            void printAssertions( std::ostream& = std::cout ) const;
            
            /**
             * Prints the first found infeasible subset of the set of received formulas.
             * @param _out The stream to print on.
             */
            void printInfeasibleSubset( std::ostream& = std::cout ) const;
            
            // Internally used interfaces
            
            /**
             * Adds a module type to this manager, for which modules can be instantiated in order to be part of the solving procedure.
             * @param _moduleType The module type to add to the module types for which modules can be instantiated in order to be 
             *                     part of the solving procedure.
             * @param _factory The factory to instantiate modules of this type.
             */
            void addModuleType( const ModuleType _moduleType, ModuleFactory* _factory )
            {
                mpModuleFactories->insert( std::pair<const ModuleType, ModuleFactory*>( _moduleType, _factory ) );
            }

            /**
             * @return All instantiated modules of the solver belonging to this manager.
             */
            const std::vector<Module*>& getAllGeneratedModules() const
            {
                return mGeneratedModules;
            }
            
            /**
             * @return A constant reference to the mapping of module types to the factories to instantiate the modules of this type.
             */
            const std::map<const ModuleType, ModuleFactory*>& rModuleFactories() const
            {
                return *mpModuleFactories;
            }
            
            /**
             * @return The stream to print the debug information on.
             */
            std::ostream& rDebugOutputChannel()
            {
                return mDebugOutputChannel;
            }

            /**
             * @return A constant reference to the managing unit for the quantifiers occurring in the formulas to solve.
             */
			const QuantifierManager& quantifierManager() const {
				return mQuantifierManager;
			}

            /**
             * @return A reference to the managing unit for the quantifiers occurring in the formulas to solve.
             */
			QuantifierManager& quantifierManager() {
				return mQuantifierManager;
			}

            /**
             * @return A constant reference to the variables, which are bound by a quantifier.
             */
			const QuantifiedVariables& quantifiedVariables() const {
				return mQuantifierManager.quantifiers();
			}

			/**
             * @return A reference to the variables, which are bound by a quantifier.
             */
			QuantifiedVariables& quantifiedVariables() {
				return mQuantifierManager.quantifiers();
			}

            /**
             * @return A constant reference to the logic this solver considers.
             */
            const Logic& logic() const
            {
                return mLogic;
            }
            
            /**
             * @return A reference to the logic this solver considers.
             */
            Logic& rLogic()
            {
                return mLogic;
            }
            
            /**
             * @return The string naming the logic this solver considers.
             */
            std::string logicToString() const
            {
                switch( mLogic )
                {
                    case Logic::QF_LIA:
                        return "QF_LIA";
                    case Logic::QF_NIA:
                        return "QF_NIA";
                    case Logic::QF_LRA:
                        return "QF_LRA";
                    default:
                        return "QF_NRA";
                }
            }
            
        protected:

            /**
             * @return A reference to the graph representing the solving strategy.
             */
            StrategyGraph& rStrategyGraph()
            {
                return mStrategyGraph;
            }

            /**
             * Gets all backends so far instantiated according the strategy and all previous enquiries of the given module.
             * @param _module The module to get all backends so far instantiated according the strategy and all previous enquiries of this module. 
             * @return All backends so far instantiated according the strategy and all previous enquiries of the given module.
             */
            std::vector<Module*> getAllBackends( Module* _module ) const
            {
                // Mutex?
                auto iter = mBackendsOfModules.find( _module );
                assert( iter != mBackendsOfModules.end() );
                std::vector<Module*> result = iter->second;
                return result;
            }
            
            /**
             * Adds the module type of a backend for the module of the type given by the given position in the manager's strategy graph. 
             * Backends of the given type will be instantiated if a module corresponding to the given position in the strategy graph asks 
             * for backends with a formula fulfilling the given conditions.
             * @param _at The position in the strategy graph to add a backend's module type.
             * @param _moduleType The module type of the backend to instantiate for modules corresponding to the given position in the 
             *                     managers strategy graph.
             * @param _conditionEvaluation A function which evaluates whether the properties of a given formula fulfill certain conditions.
             * @return The position in this managers strategy graph corresponding to the added module type.
             */
            size_t addBackendIntoStrategyGraph( size_t _at, ModuleType _moduleType, ConditionEvaluation _conditionEvaluation = isCondition )
            {
                return mStrategyGraph.addBackend( _at, _moduleType, _conditionEvaluation );
            }

            /**
             * Extends the strategy graph of this manager such that if a module corresponding to the first given position in the
             * strategy graph asks for backends for a formula whose properties satisfy the conditions checked by the given function pointer,
             * the this manager instantiates (if not yet instantiated) a backend corresponding to the second given position in the 
             * strategy graph.
             * @param _from The position in the strategy graph to which the enquiring module corresponds to.
             * @param _to The position in the strategy graph to which the instantiated backend for this enquiry corresponds to.
             * @param _conditionEvaluation A function which evaluates whether the properties of a given formula fulfill certain conditions.
             */
            void addBacklinkIntoStrategyGraph( size_t _from, size_t _to, ConditionEvaluation _conditionEvaluation = isCondition )
            {
                mStrategyGraph.addBacklink( _from, _to, _conditionEvaluation );
            }

            #ifdef SMTRAT_STRAT_PARALLEL_MODE
            /**
             * @return true, if we might run in parallel eventually;
             *         false, otherwise.
             */
            bool runsParallel() const
            {
                return mRunsParallel;
            }
            #endif

            /**
             * Get the backends to call for the given problem instance required by the given module.
             *
             * @param _formula     The problem instance.
             * @param _requiredBy  The module asking for a backend.
             * @param _foundAnswer A conditional
             *
             * @return  A vector of modules, which the module defined by _requiredBy calls in parallel to achieve
             *           an answer to the given instance.
             */
            std::vector<Module*> getBackends( Module*, std::atomic_bool* );
            
            #ifdef SMTRAT_STRAT_PARALLEL_MODE
            /**
             * Submits an enquiry of a module to solve its passed formula.
             * @param _module The module which wants its passed formula to be solved.
             * @return A future containing the answer, as soon as the enquiry has been processed.
             */
            std::future<Answer> submitBackend( Module* _module );
            
            /**
             * 
             * @param _module
             */
            void checkBackendPriority( Module* _module );
            #endif
    };
}    // namespace smtrat
#endif   /** SMTRAT_MANAGER_H */
