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

#pragma once

#include <vector>

#include "StrategyGraph.h"
#include "SolverStatistics.h"
#ifdef SMTRAT_STRAT_PARALLEL_MODE
#include "ThreadPool.h"
#endif

#include <smtrat-common/smtrat-common.h>
#include "ModuleInput.h"
#include "Module.h"

namespace smtrat
{   
    class Module; // forward declaration
    //class ModuleFactory; // forward declaration
    
    /**
     * Base class for solvers. This is the interface to the user.
     **/
    class Manager
    {
        friend class Module;
        private:

            /// a vector of flags, which indicate that an answer has been found of an antecessor module of the primary module
            smtrat::Conditionals mPrimaryBackendFoundAnswer;
            /// the constraints so far passed to the primary backend
            ModuleInput* mpPassedFormula;
            /// The propositions of the passed formula.
            carl::Condition mPropositions;
            /// Contains the backtrack points, that are iterators to the last formula to be kept when backtracking to the respective point.
            std::vector<ModuleInput::iterator> mBacktrackPoints;
            /// all generated instances of modules
            std::vector<Module*> mGeneratedModules;
            /// a mapping of each module to its backends
            std::map<const Module* const, std::vector<Module*> > mBackendsOfModules;
            /// the primary backends
            Module* mpPrimaryBackend;
            /// a Boolean showing whether the manager has received new constraint after the last consistency check
            bool mBackendsUptodate;
            /// primary strategy
			StrategyGraph mStrategyGraph;
            /// channel to write debug output
            std::ostream mDebugOutputChannel;
            /// the logic this solver considers
            carl::Logic mLogic;
			/// List of formula which are relevant for certain tasks
			std::set<FormulaT> mInformationRelevantFormula;
			/// Level of lemma generation
			LemmaLevel mLemmaLevel;
            /// objective variable
            carl::Variable mObjectiveVariable;
            #ifdef SMTRAT_DEVOPTION_Statistics
            /// Stores all statistics for the solver this manager belongs to.
            SolverStatistics& mStatistics = statistics_get<SolverStatistics>("Solver");
            #endif
            #ifdef SMTRAT_STRAT_PARALLEL_MODE
            /// contains all threads to assign jobs to
            ThreadPool* mpThreadPool;
            /// the number of branches occurring in the strategy (the same as the number of leaves)
            size_t mNumberOfBranches;
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
            bool inform( const FormulaT& _constraint );
            
            /**
             * The inverse of informing about a constraint. All data structures which were kept regarding this
             * constraint are going to be removed. Note, that this makes only sense if it is not likely enough
             * that a formula with this constraint must be solved again.
             * @param _constraint The constraint to remove from internal data structures.
             */
            void deinform( const FormulaT& _constraint );

            /**
             * Adds the given formula to the conjunction of formulas, which will be considered for the next 
             * satisfiability check.
             * @param _subformula The formula to add.
             * @param _containsUnknownConstraints true, if the formula to add contains constraints, about which this solver 
             *                                    was not yet informed.
             * @return false, if it is easy to decide whether adding this formula creates a conflict;
             *          true, otherwise.
             */
            bool add( const FormulaT& _subformula, bool _containsUnknownConstraints = true );

            /**
             * Checks the so far added formulas for satisfiability.
             * @return True, if the conjunction of the so far added formulas is satisfiable;
             *          False, if it not satisfiable;
             *          Unknown, if this solver cannot decide whether it is satisfiable or not.
             */
            Answer check( bool _full = true );
            
            /**
             * Pushes a backtrack point to the stack of backtrack points.
             * 
             * Note, that this interface has not necessarily be used to apply a solver constructed
             * with SMT-RAT, but is often required by state-of-the-art SMT solvers when embedding
             * a theory solver constructed with SMT-RAT into them.
             */
            void push()
            {
				// Pushes iterator to last formula contained in the backtrack point.
				auto it = mpPassedFormula->end();
				// If the list is empty use end(), otherwise an iterator to the last element
				if (!mpPassedFormula->empty()) --it;
                mBacktrackPoints.emplace_back(it);
            }
            
            /**
             * Pops a backtrack point from the stack of backtrack points. This provokes, that
             * all formulas which have been added after that backtrack point are removed.
             * 
             * Note, that this interface has not necessarily be used to apply a solver constructed
             * with SMT-RAT, but is often required by state-of-the-art SMT solvers when embedding
             * a theory solver constructed with SMT-RAT into them.
             */
            bool pop();
            
            void pop( size_t _levels );
            
            void clear()
            {
                while( pop() );
            }

            void setObjectiveVariable(carl::Variable var) {
                mObjectiveVariable = var;
            }

            const carl::Variable& objectiveVariable() const {
                return mObjectiveVariable;
            }
            
			void takeObjectiveVariable(const Manager& m) {
				mObjectiveVariable = m.objectiveVariable();
			}
            
            void reset();
            
            /**
             * @return All infeasible subsets of the set so far added formulas.
             * 
             * Note, that the conjunction of the so far added formulas must be inconsistent to
             * receive an infeasible subset.
             */
            const std::vector<FormulaSetT>& infeasibleSubsets() const;

            /**
             * Determines variables assigned by the currently found satisfying assignment to an equal value in their domain.
             * @return A list of vectors of variables, stating that the variables in one vector are assigned to equal values.
             */
			std::list<std::vector<carl::Variable>> getModelEqualities() const;

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
            const Model& model() const;

			/**
			 * @return A list of all assignments, such that they satisfy the conjunction of
			 *          the so far added formulas.
			 *
			 * Note, that an assignment is only provided if the conjunction of so far added
			 * formulas is satisfiable. Furthermore, when solving non-linear real arithmetic
			 * formulas the assignment could contain other variables or freshly introduced
			 * variables.
			 */
			const std::vector<Model>& allModels() const
			{
				mpPrimaryBackend->updateAllModels();
				return mpPrimaryBackend->allModels();
			}
            
            /**
             * Returns the lemmas/tautologies which were made during the last solving provoked by check(). These lemmas
             * can be used in the same manner as infeasible subsets are used.
             * @return The lemmas/tautologies made during solving.
             */
            std::vector<FormulaT> lemmas();

            /**
             * @return The conjunction of so far added formulas.
             */
            const ModuleInput& formula() const
            {
                return *mpPassedFormula;
            }

            // @todo: we want a const_iterator here, but gcc 4.8 doesn't allow us :( even though it should
            ModuleInput::iterator formulaBegin()
            {
                return mpPassedFormula->begin();
            }
            ModuleInput::iterator formulaEnd()
            {
                return mpPassedFormula->end();
            }
            
            /**
             * Prints the currently found assignment of variables occurring in the so far 
             * added formulas to values of their domains, if the conjunction of these 
             * formulas is satisfiable.
             * @param The stream to print on.
             */
            void printAssignment() const;
            
            /**
             * Prints all assignments of variables occurring in the so far 
             * added formulas to values of their domains, if the conjunction of these 
             * formulas is satisfiable.
             * @param The stream to print on.
             */
            void printAllAssignments( std::ostream& _out = std::cout )
            {
                mpPrimaryBackend->printAllModels( _out );
            }
                
            /**
             * Prints the first found infeasible subset of the set of received formulas.
             * @param _out The stream to print on.
             */
            void printInfeasibleSubset( std::ostream& = std::cout ) const;
            
            /**
             * Prints the stack of backtrack points.
             * @param _out The stream to print on.
             */
            void printBackTrackStack( std::ostream& = std::cout ) const;
            
            /**
             * Prints the strategy of the solver maintained by this manager.
             * @param _out The stream to print on.
             */
            void printStrategyGraph( std::ostream& _os = std::cout ) const
            {
                _os << mStrategyGraph << std::endl;
            }
            
            // Internally used interfaces
            
            /**
             * @return All instantiated modules of the solver belonging to this manager.
             */
            const std::vector<Module*>& getAllGeneratedModules() const
            {
                return mGeneratedModules;
            }
            
            /**
             * @return The stream to print the debug information on.
             */
            std::ostream& rDebugOutputChannel()
            {
                return mDebugOutputChannel;
            }

            /**
             * @return A constant reference to the logic this solver considers.
             */
            auto logic() const {
                return mLogic;
            }
            
            /**
             * @return A reference to the logic this solver considers.
             */
            auto& rLogic() {
                return mLogic;
            }

			/**
			 * Adds formula to InformationRelevantFormula
			 * @param formula Formula to add
			 */
			inline void addInformationRelevantFormula( const FormulaT& formula )
			{
				mInformationRelevantFormula.insert( formula );
			}

			/**
			* Deletes all InformationRelevantFormula
			*/
			inline void clearInformationRelevantFormula()
			{
				mInformationRelevantFormula.clear();
			}

			/**
			 * Sets the current level for lemma generation
			 * @param level Level
			 */
			inline void setLemmaLevel(LemmaLevel level)
			{
				mLemmaLevel = level;
			}

			/**
			 * Checks if current lemma level is greater or equal to given level.
			 * @param level Level to check.
			 */
			inline bool isLemmaLevel(LemmaLevel level)
			{
				return level <= mLemmaLevel;
			}
            
            /**
             * @return A pair of a Boolean and a formula, where the Boolean is true, if the input formula 
             *         could be simplified to an equisatisfiable formula. The formula is equisatisfiable to this
             *         solver's input formula, if the Boolean is true.
             */
            std::pair<bool,FormulaT> getInputSimplified();

            /**
             * Removes the formula at the given position in the conjunction of formulas,
             * which will be considered for the next satisfiability check.
             * @param _subformula The position of the formula to remove.
             * @return An iterator to the formula after the position of the just removed
             *          formula. If the removed formula has been the last element, the 
             *          end of the conjunction of formulas, which will be considered for the 
             *          next satisfiability check is returned.
             */
            ModuleInput::iterator remove( ModuleInput::iterator _subformula ); // @todo: we want a const_iterator here, but gcc 4.8 doesn't allow us :( even though it should
            
            /**
             * Temporarily added: (TODO: Discuss with Gereon)
             * Removes the given formula in the conjunction of formulas,
             * which will be considered for the next satisfiability check.
             * @param _subformula The formula to remove.
             * @return An iterator to the formula after the position of the just removed
             *          formula. If the removed formula has been the last element, the
             *          end of the conjunction of formulas, which will be considered for the
             *          next satisfiability check is returned.
             */
            ModuleInput::iterator remove( const FormulaT& _subformula )
            {
                return remove( mpPassedFormula->find( _subformula ) );
            }

        protected:
			
		 	void setStrategy(const std::initializer_list<BackendLink>& backends) {
				std::size_t id = mStrategyGraph.addRoot(backends);
				std::size_t priority = mpPrimaryBackend->threadPriority().first;
				mpPrimaryBackend->setThreadPriority(thread_priority(priority, id));
				SMTRAT_LOG_INFO("smtrat.strategygraph", "Strategygraph:" << std::endl << mStrategyGraph);
				SMTRAT_LOG_INFO("smtrat.strategygraph", "Branches: " << mStrategyGraph.numberOfBranches());
			}
			void setStrategy(const BackendLink& backend) {
				setStrategy({backend});
			}
			template<typename Module>
			BackendLink addBackend(const std::initializer_list<BackendLink>& backends = {}) {
				return mStrategyGraph.addBackend<Module>(backends);
			}
			template<typename Module>
			BackendLink addBackend(const BackendLink& backend) {
				return mStrategyGraph.addBackend<Module>({backend});
			}
			BackendLink& addEdge(std::size_t from, std::size_t to) {
				return mStrategyGraph.addEdge(from, to);
			}
            /**
             * Gets all backends so far instantiated according the strategy and all previous enquiries of the given module.
             * @param _module The module to get all backends so far instantiated according the strategy and all previous enquiries of this module. 
             * @return All backends so far instantiated according the strategy and all previous enquiries of the given module.
             */
            std::vector<Module*> getAllBackends( Module* _module ) const
            {
                #ifdef SMTRAT_STRAT_PARALLEL_MODE
                std::lock_guard<std::mutex> lock( mBackendsMutex );
                #endif
                auto iter = mBackendsOfModules.find( _module );
                assert( iter != mBackendsOfModules.end() );
                std::vector<Module*> result = iter->second;
                return result;
            }
			
            #ifdef SMTRAT_STRAT_PARALLEL_MODE
            /**
             * @return true, if we might run in parallel eventually;
             *         false, otherwise.
             */
            bool runsParallel()
            {
				initialize();
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
#ifdef __VS
            std::vector<Module*> getBackends( Module*, std::atomic<bool>* );
#else
            std::vector<Module*> getBackends( Module*, std::atomic_bool* );
#endif
            
            #ifdef SMTRAT_STRAT_PARALLEL_MODE
            /**
             * Submits an enquiry of a module to solve its passed formula.
             * @param _module The module which wants its passed formula to be solved.
             * @param _full false, if this module should avoid too expensive procedures and rather return unknown instead.
             * @param _objective
             * @return A future containing the answer, as soon as the enquiry has been processed.
             */
			Answer runBackends(const std::vector<Module*>& modules, bool final, bool full, carl::Variable::Arg objective);
            #endif

			/**
			 * Gets all InformationRelevantFormulas
			 * @return Set of all formulas
             */
			inline const std::set<FormulaT>& getInformationRelevantFormulas()
			{
				return mInformationRelevantFormula;
			}
    };
}    // namespace smtrat
