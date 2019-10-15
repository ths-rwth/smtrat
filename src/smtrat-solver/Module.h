/**
 * @file Module.h
 * @author Florian Corzilius
 * @author Ulrich Loup
 * @author Sebastian Junges
 * @since 2012-01-18
 * @version 2013-02-06
 */

#pragma once

/// Flag activating some informative and not exaggerated output about module calls.
//#define GENERATE_ONLY_PARSED_FORMULA_INTO_ASSUMPTIONS
#ifdef GENERATE_ONLY_PARSED_FORMULA_INTO_ASSUMPTIONS
#ifndef SMTRAT_DEVOPTION_Validation
//#define SMTRAT_DEVOPTION_Validation
#endif
#endif


#include <vector>
#include <set>
#include <string>
#include <chrono>
#include <atomic>
#include <mutex>
#include <carl-model/Assignment.h>
#include <carl/util/TimingCollector.h>
#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/statistics/Statistics.h>
#include <smtrat-common/statistics/StatisticsCollector.h>
#include "ModuleInput.h"

namespace smtrat
{
    class Manager; // forward declaration

    /// A vector of atomic bool pointers.
    typedef std::vector<std::atomic_bool*> Conditionals;
    
    /**
     * Stores all necessary information of an branch, which can be used to detect probable infinite loop of branchings.
     */
    struct Branching
    {
        /// The polynomial to branch at.
#ifdef __VS
		Poly::PolyType mPolynomial;
#else
        typename Poly::PolyType mPolynomial;
#endif
        /// The value to branch the polynomial at.
        Rational mValue;
        /// The number of repetitions of the branching.
        size_t mRepetitions;
        /**
         * Stores whether this the branching of the polynomial has been on an increasing sequence of values (>0),
         * or on a decreasing sequence of values (<0). It is initially zero.
         */
        int mIncreasing;

        /**
         * Constructor.
         * @param _polynomial The polynomial to branch at.
         * @param _value The value to branch the polynomial at.
         */
#ifdef __VS
		Branching(const Poly::PolyType& _polynomial, const Rational& _value) :
#else
        Branching( const typename Poly::PolyType& _polynomial, const Rational& _value ):
#endif
            mPolynomial( _polynomial ),
            mValue( _value ),
            mRepetitions( 1 ),
            mIncreasing( 0 )
        {}
    };
    
    /**
     * A base class for all kind of theory solving methods.
     */
    class Module
    {
        friend Manager;
        public:
			struct ModuleStatistics: public Statistics {
#ifdef SMTRAT_DEVOPTION_Statistics
				carl::timing::time_point timer_add_started;
				carl::timing::time_point timer_check_started;
				carl::timing::time_point timer_remove_started;
				carl::timing::time_point timer_pause_started;
				carl::timing::duration timer_add_total;
				carl::timing::duration timer_check_total;
				carl::timing::duration timer_remove_total;
				bool timer_add_running;
				bool timer_check_running;
				bool timer_remove_running;
				std::size_t check_count = 0;

				void collect() override {
					addKeyValuePair("timer_add_total", timer_add_total.count());
					addKeyValuePair("timer_check_total", timer_check_total.count());
					addKeyValuePair("timer_remove_total", timer_remove_total.count());
					addKeyValuePair("check_count", check_count);
				}

				void start_add() { timer_add_started = carl::timing::now(); }
				void start_check() { timer_check_started = carl::timing::now(); }
				void start_remove() { timer_remove_started = carl::timing::now(); }
				void pause_all() { timer_pause_started = carl::timing::now(); }
				void continue_all() {
					auto diff = carl::timing::since(timer_pause_started);
					timer_add_started += diff;
					timer_check_started += diff;
					timer_remove_started += diff;
				}
				void stop_add() { timer_add_total += carl::timing::since(timer_add_started); }
				void stop_check() { timer_check_total += carl::timing::since(timer_check_started); }
				void stop_remove() { timer_remove_total += carl::timing::since(timer_remove_started); }
#else
				void start_add() {}
				void start_check() {}
				void start_remove() {}
				void pause_all() {}
				void continue_all() {}
				void stop_add() {}
				void stop_check() {}
				void stop_remove() {}
#endif
			};

            /// For time measuring purposes.
            typedef std::chrono::microseconds timeunit;
            /*
             * The type of a lemma.
             *     PERMANENT = The lemma should not be forgotten.
             */
            enum class LemmaType: unsigned { NORMAL = 0, PERMANENT = 1 };
            
            struct Lemma
            {
                /// The lemma to learn.
                FormulaT mLemma;
                /// The type of the lemma.
                LemmaType mLemmaType;
                /// The formula within the lemma, which should be assigned to true in the next decision.
                FormulaT mPreferredFormula;

                /**
                 * Constructor.
                 * @param _lemma The lemma to learn.
                 * @param _lemmaType The type of the lemma.
                 * @param _preferredFormula The formula within the lemma, which should be assigned to true in the next decision.
                 */
                Lemma( const FormulaT& _lemma, const LemmaType& _lemmaType, const FormulaT& _preferredFormula ):
                    mLemma( _lemma ),
                    mLemmaType( _lemmaType ),
                    mPreferredFormula( _preferredFormula )
                {}
            };
            
            struct TheoryPropagation
            {
                /// The constraints under which the propagated constraint holds.
                FormulasT mPremise;
                /// The propagated constraint.
                FormulaT mConclusion;
                
                /**
                 * Constructor.
                 */
                TheoryPropagation( FormulasT&& _premise, const FormulaT& _conclusion ):
                    mPremise( std::move( _premise ) ),
                    mConclusion( _conclusion )
                {}
                
                TheoryPropagation() = delete;
                TheoryPropagation( const TheoryPropagation& ) = delete;
                TheoryPropagation( TheoryPropagation&& _toMove ):
                    mPremise( std::move( _toMove.mPremise ) ),
                    mConclusion( std::move(_toMove.mConclusion) )
                {}
                
                
                TheoryPropagation& operator=( const TheoryPropagation& _toMove ) = delete;
                TheoryPropagation& operator=( TheoryPropagation&& _toMove )
                {
                    mPremise = std::move( _toMove.mPremise );
                    mConclusion = std::move( _toMove.mConclusion );
                    return *this;
                }
                
                ~TheoryPropagation() {}
            };

        // Members.
        private:
            /// A unique ID to identify this module instance. (Could be useful but currently nowhere used)
            std::size_t mId;
            /// The priority of this module to get a thread for running its check procedure.
            thread_priority mThreadPriority;
            /// The formula passed to this module.
            const ModuleInput* mpReceivedFormula;
            /// The formula passed to the backends of this module.
            ModuleInput* mpPassedFormula;
			std::string mModuleName;
			ModuleStatistics& mStatistics = statistics_get<ModuleStatistics>(moduleName());
        protected:
            /// Stores the infeasible subsets.
            std::vector<FormulaSetT> mInfeasibleSubsets;
            /// A reference to the manager.
            Manager* const mpManager;
            /// Stores the assignment of the current satisfiable result, if existent.
            mutable Model mModel;
			/// Stores all satisfying assignments
			mutable std::vector<Model> mAllModels;
            /// True, if the model has already been computed.
            mutable bool mModelComputed;
            /// true, if the check procedure should perform a final check which especially means not to postpone splitting decisions
            bool mFinalCheck;
            /// false, if this module should avoid too expensive procedures and rather return unknown instead.
            bool mFullCheck;
            /// Objective variable to be minimized. If set to NO_VARIABLE, a normal sat check should be performed.
            carl::Variable mObjectiveVariable;
            ///
            std::vector<TheoryPropagation> mTheoryPropagations;

        //private:
            /// States whether the received formula is known to be satisfiable or unsatisfiable otherwise it is set to unknown.
            std::atomic<Answer> mSolverState;
            /// This flag is passed to any backend and if it determines an answer to a prior check call, this flag is fired.
#ifdef __VS
            std::atomic<bool>* mBackendsFoundAnswer;
#else
            std::atomic_bool* mBackendsFoundAnswer;
#endif
            /// Vector of Booleans: If any of them is true, we have to terminate a running check procedure.
            Conditionals mFoundAnswer;
            /// The backends of this module which are currently used (conditions to use this module are fulfilled for the passed formula).
            std::vector<Module*> mUsedBackends;
            /// The backends of this module which have been used.
            std::vector<Module*> mAllBackends;
            /// Stores the lemmas being valid formulas this module or its backends made.
            std::vector<Lemma> mLemmas;
            /// Stores the position of the first sub-formula in the passed formula, which has not yet been considered for a consistency check of the backends.
            ModuleInput::iterator mFirstSubformulaToPass;
            /// Stores the constraints which the backends must be informed about.
            carl::FastSet<FormulaT> mConstraintsToInform;
            /// Stores the position of the first constraint of which no backend has been informed about.
            carl::FastSet<FormulaT> mInformedConstraints;
            /// Stores the position of the first (by this module) unchecked sub-formula of the received formula.
            ModuleInput::const_iterator mFirstUncheckedReceivedSubformula;
            /// Counter used for the generation of the smt2 files to check for smaller muses.
            mutable unsigned mSmallerMusesCheckCounter;
            /// Maps variables to the number of their occurrences
            std::vector<std::size_t> mVariableCounters;

        public:
            #ifdef SMTRAT_STRAT_PARALLEL_MODE
            /// a mutex for exclusive access to the old splitting variables
            static std::mutex mOldSplittingVarMutex;
            #define OLD_SPLITTING_VARS_LOCK_GUARD std::lock_guard<std::mutex> lock( mOldSplittingVarMutex );
            #define OLD_SPLITTING_VARS_LOCK mOldSplittingVarMutex.lock();
            #define OLD_SPLITTING_VARS_UNLOCK mOldSplittingVarMutex.unlock();
            #else
            #define OLD_SPLITTING_VARS_LOCK_GUARD
            #define OLD_SPLITTING_VARS_LOCK
            #define OLD_SPLITTING_VARS_UNLOCK
            #endif

            /**
             * Constructs a module.
             * @param type The type of this module.
             * @param _formula The formula passed to this module, called received formula.
             * @param _foundAnswer Vector of Booleans: If any of them is true, we have to terminate a running check procedure.
             * @param _manager A reference to the manager of the solver using this module.
             */
            Module( const ModuleInput* _formula, Conditionals& _foundAnswer, Manager* _manager = nullptr, std::string module_name = "Module" );
            
            /**
             * Destructs a module.
             */
            virtual ~Module();

            /// Contains the assumptions made, which can be stored in an smtlib-file and be verified later by an external tool.
            static std::vector<std::string> mAssumptionToCheck;
            /// All variables occurring in the assumptions made, which can be stored in an smtlib-file and be verified later by an external tool.
            static std::set<std::string> mVariablesInAssumptionToCheck;
            /// The number of different variables to consider for a probable infinite loop of branchings.
            static size_t mNumOfBranchVarsToStore;
            /// Stores the last branches in a cycle buffer.
            static std::vector<Branching> mLastBranches;
            /// The beginning of the cyclic buffer storing the last branches.
            static size_t mFirstPosInLastBranches;
            /// Reusable splitting variables.
            static std::vector<FormulaT> mOldSplittingVariables;

            // Main interfaces
            
            /**
             * Informs the module about the given constraint. It should be tried to inform this
             * module about any constraint it could receive eventually before assertSubformula
             * is called (preferably for the first time, but at least before adding a formula
             * containing that constraint).
             * @param _constraint The constraint to inform about.
             * @return false, if it can be easily decided whether the given constraint is inconsistent;
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
             * Informs all backends about the so far encountered constraints, which have not yet been communicated.
             * This method must not be called twice and only before the first runBackends call.
             */
			virtual void init();
            
            /**
             * The module has to take the given sub-formula of the received formula into account.
             *
             * @param _subformula The sub-formula to take additionally into account.
             * @return false, if it can be easily decided that this sub-formula causes a conflict with
             *          the already considered sub-formulas;
             *          true, otherwise.
             */
            bool add( ModuleInput::const_iterator _subformula );
            
            /**
             * Checks the received formula for consistency. Note, that this is an implementation of 
             * the satisfiability check of the conjunction of the so far received formulas, which does
             * actually nothing but passing the problem to its backends. This implementation is only used
             * internally and must be overwritten by any derived module.
             * @param _final true, if this satisfiability check will be the last one (for a global sat-check), if its result is SAT
             * @param _full false, if this module should avoid too expensive procedures and rather return unknown instead.
             * @param _objective if not set to NO_VARIABLE, the module should find an assignment minimizing this objective variable; otherwise any assignment is good.
             * @return True,    if the received formula is satisfiable;
             *         False,   if the received formula is not satisfiable;
             *         Unknown, otherwise.
             */
            virtual Answer check( bool _final = false, bool _full = true, carl::Variable _objective = carl::Variable::NO_VARIABLE );
            
            /**
             * Removes everything related to the given sub-formula of the received formula. However,
             * it is desired not to lose track of search spaces where no satisfying  assignment can 
             * be found for the remaining sub-formulas.
             *
             * @param _subformula The sub formula of the received formula to remove.
             */
            virtual void remove( ModuleInput::const_iterator _subformula );
            
            /**
             * Updates the model, if the solver has detected the consistency of the received formula, beforehand.
             */
            virtual void updateModel() const;

			/**
			 * Updates all satisfying models, if the solver has detected the consistency of the received formula, beforehand.
			 */
			virtual void updateAllModels();
            
			/**
             * Partition the variables from the current model into equivalence classes according to their assigned value.
             * 
             * The result is a set of equivalence classes of variables where all variables within one class are assigned the same value.
             * Note that the number of classes may not be minimal, i.e. two classes may actually be equivalent.
             * @return Equivalence classes.
             */
            virtual std::list<std::vector<carl::Variable>> getModelEqualities() const;
            
            /**
             * @return 0, if the given formula is conflicted by the current model;
             *         1, if the given formula is satisfied by the current model;
             *         2, otherwise
             *         3, if we do not know anything (default)
             */
            unsigned currentlySatisfiedByBackend( const FormulaT& _formula ) const;
            
            /**
             * @return 0, if the given formula is conflicted by the current model;
             *         1, if the given formula is satisfied by the current model;
             *         2, otherwise;
             *         3, if we do not know anything (default)
             */
            virtual unsigned currentlySatisfied( const FormulaT& ) const
            {
                return 3;
            }
            
            bool receivedVariable( carl::Variable::Arg _var ) const
            {
                return _var.id() < mVariableCounters.size() && mVariableCounters[_var.id()] > 0;
            }

            // Methods to read and write on the members.
            /**
             * @return True, if this module is in a state, such that it has found a solution for its received formula;
             *         False, if this module is in a state, such that it has determined that there is no solution for its received formula;
             *         Unknown, otherwise.
             */
            inline Answer solverState() const
            {
                return mSolverState.load();
            }

            /**
             * @return A unique ID to identify this module instance.
             */
            inline std::size_t id() const
            {
                return mId;
            }

            /**
             * Sets this modules unique ID to identify itself.
             * @param _id The id to set this module's id to.
             */
            void setId( std::size_t _id )
            {
                assert( mId == 0 && _id != 0 );
                mId = _id;
            }

            /**
             * @return The priority of this module to get a thread for running its check procedure.
             */
            inline thread_priority threadPriority() const
            {
                return mThreadPriority;
            }

            /**
             * Sets the priority of this module to get a thread for running its check procedure.
             * @param _threadPriority The priority to set this module's thread priority to.
             */
            void setThreadPriority( thread_priority _threadPriority )
            {
                mThreadPriority = _threadPriority;
            }

            /**
             * @return A pointer to the formula passed to this module.
             */
            inline const ModuleInput* pReceivedFormula() const
            {
                return mpReceivedFormula;
            }

            /**
             * @return A reference to the formula passed to this module.
             */
            inline const ModuleInput& rReceivedFormula() const
            {
                return *mpReceivedFormula;
            }

            /**
             * @return A pointer to the formula passed to the backends of this module.
             */
            inline const ModuleInput* pPassedFormula() const
            {
                return mpPassedFormula;
            }

             /**
             * @return A reference to the formula passed to the backends of this module.
             */
            inline const ModuleInput& rPassedFormula() const
            {
                return *mpPassedFormula;
            }

            /**
             * @return The assignment of the current satisfiable result, if existent.
             */
            inline const Model& model() const
            {
                return mModel;
            }

			/**
			 * @return All satisfying assignments, if existent.
			 */
			inline const std::vector<Model>& allModels() const
			{
				return mAllModels;
			}

            /**
             * @return The infeasible subsets of the set of received formulas (empty, if this module has not
             *          detected unsatisfiability of the conjunction of received formulas.
             */
            inline const std::vector<FormulaSetT>& infeasibleSubsets() const
            {
                return mInfeasibleSubsets;
            }

            /**
             * @return The backends of this module which are currently used (conditions to use this module are fulfilled for the passed formula).
             */
            const std::vector<Module*>& usedBackends() const
            {
                return mUsedBackends;
            }

            /**
             * @return The constraints which the backends must be informed about.
             */
            const carl::FastSet<FormulaT>& constraintsToInform() const
            {
                return mConstraintsToInform;
            }

            /**
             * @return The position of the first constraint of which no backend has been informed about.
             */
            const carl::FastSet<FormulaT>& informedConstraints() const
            {
                return mInformedConstraints;
            }
            
            static void freeSplittingVariable( const FormulaT& _splittingVariable )
            {
                OLD_SPLITTING_VARS_LOCK_GUARD
                mOldSplittingVariables.push_back( _splittingVariable ); 
            }

            /**
             * Stores a lemma being a valid formula.
             * @param _lemma The eduction/lemma to store.
             * @param _lt The type of the lemma.
             */
            void addLemma( const FormulaT& _lemma, const LemmaType& _lt = LemmaType::NORMAL, const FormulaT& _preferredFormula = FormulaT( carl::FormulaType::TRUE ) )
            {
                #ifdef SMTRAT_DEVOPTION_Validation
                if (Settings().validation.log_lemmata) {
                    addAssumptionToCheck( FormulaT( carl::FormulaType::NOT, _lemma ), false, moduleName() + "_lemma" );
                }
                #endif
                mLemmas.emplace_back( _lemma, _lt, _preferredFormula );
            }

            /**
             * Checks whether this module or any of its backends provides any lemmas.
             */
            bool hasLemmas()
            {
                if( !mLemmas.empty() )
                    return true;
                if( mpManager != nullptr )
                {
                    for( auto module = mAllBackends.begin(); module != mAllBackends.end(); ++module )
                    {
                        if( (*module)->hasLemmas() )
                            return true;
                    }
                }
                return false;
            }

            /**
             * Deletes all yet found lemmas.
             */
            void clearLemmas()
            {
                if( mpManager != nullptr )
                {
                    for( auto module = mAllBackends.begin(); module != mAllBackends.end(); ++module )
                    {
                        (*module)->clearLemmas();
                    }
                }
                mLemmas.clear();
            }

            /**
             * @return A constant reference to the lemmas being valid formulas this module or its backends made.
             */
            const std::vector<Lemma>& lemmas() const
            {
                return mLemmas;
            }

            /**
             * @return The position of the first (by this module) unchecked sub-formula of the received formula.
             */
            ModuleInput::const_iterator firstUncheckedReceivedSubformula() const
            {
                return mFirstUncheckedReceivedSubformula;
            }

            /**
             * @return The position of the first sub-formula in the passed formula, which has not yet been considered for a consistency check of the backends.
             */
            ModuleInput::const_iterator firstSubformulaToPass() const
            {
                return mFirstSubformulaToPass;
            }

            /**
             * Notifies that the received formulas has been checked.
             */
            void receivedFormulaChecked()
            {
                mFirstUncheckedReceivedSubformula = mpReceivedFormula->end();
            }

            /**
             * @return A vector of Booleans: If any of them is true, we have to terminate a running check procedure.
             */
            const smtrat::Conditionals& answerFound() const
            {
                return mFoundAnswer;
            }
            
            /**
             * @return true, if this module is a preprocessor that is a module, which simplifies
             *         its received formula to an equisatisfiable formula being passed to its backends.
             *         The simplified formula can be obtained with getReceivedFormulaSimplified().
             */
            bool isPreprocessor() const
            {
                return false;
            }
            
            /**
             * @return The name of the given module type as name.
             */
            virtual std::string moduleName() const {
				return mModuleName;
			}
            
            carl::Variable objective() const {
                return mObjectiveVariable;
            }

            bool is_minimizing() const {
                return mObjectiveVariable != carl::Variable::NO_VARIABLE;
            }

            /**
             * Excludes all variables from the current model, which do not occur in the received formula.
             */
            void excludeNotReceivedVariablesFromModel() const;
            
            /**
             * Stores all lemmas of any backend of this module in its own lemma vector.
             */
            void updateLemmas();
            void collectTheoryPropagations();
            
            /**
             * Collects the formulas in the given formula, which are part of the received formula. If the given formula directly
             * occurs in the received formula, it is inserted into the given set. Otherwise, the given formula must be of 
             * type AND and all its sub-formulas part of the received formula. Hence, they will be added to the given set.
             * @param _formula The formula from which to collect the formulas being sub-formulas of the received formula (origins).
             * @param _origins The set in which to store the origins.
             */
            void collectOrigins( const FormulaT& _formula, FormulasT& _origins ) const;
            void collectOrigins( const FormulaT& _formula, FormulaSetT& _origins ) const;

            // Methods for debugging purposes.
            /**
             * Add a formula to the assumption vector and its predetermined consistency status.
             * @param _formula The formula which should be consistent/inconsistent.
             * @param _consistent A flag indicating whether the conjunction of the given constraints should be
             *         consistent or inconsistent.
             * @param _label A label which will be encoded as a Boolean variable into the formula to represent the 
             *               assumption, while keeping it equisatisfiable (the label could, e.g., be the name of the module
             *               or its sub-procedure).
             * @see Module::storeAssumptionsToCheck
             */
            static void addAssumptionToCheck( const FormulaT& _formula, bool _consistent, const std::string& _label );
            
            /**
             * Add a formula to the assumption vector and its predetermined consistency status.
             * @param _subformulas The sub-formulas whose conjunction should be consistent/inconsistent.
             * @param _consistent A flag indicating whether the conjunction of the given constraints should be
             *         consistent or inconsistent.
             * @param _label A label which will be encoded as a Boolean variable into the formula to represent the 
             *               assumption, while keeping it equisatisfiable (the label could, e.g., be the name of the module
             *               or its sub-procedure).
             * @see Module::storeAssumptionsToCheck
             */
            static void addAssumptionToCheck( const ModuleInput& _formula, bool _consistent, const std::string& _label );
			static void addAssumptionToCheck( const ModuleInput& _subformulas, Answer _status, const std::string& _label );
            
            /**
             * Add a conjunction of formulas to the assumption vector and its predetermined consistency status.
             * @param _formulas The formulas, whose conjunction should be consistent/inconsistent.
             * @param _consistent A flag indicating whether the conjunction of the given constraints should be
             *         consistent or inconsistent.
             * @param _label A label which will be encoded as a Boolean variable into the formula to represent the 
             *               assumption, while keeping it equisatisfiable (the label could, e.g., be the name of the module
             *               or its sub-procedure).
             * @see Module::storeAssumptionsToCheck
             */
            static void addAssumptionToCheck( const FormulasT& _formulas, bool _consistent, const std::string& _label );
            static void addAssumptionToCheck( const FormulaSetT& _formulas, bool _consistent, const std::string& _label );
            /**
             * Add a conjunction of _constraints to the assumption vector and its predetermined consistency status.
             * @param _constraints The constraints, whose conjunction should be consistent/inconsistent.
             * @param _consistent A flag indicating whether the conjunction of the given constraints should be
             *         consistent or inconsistent.
             * @param _label A label which will be encoded as a Boolean variable into the formula to represent the 
             *               assumption, while keeping it equisatisfiable (the label could, e.g., be the name of the module
             *               or its sub-procedure).
             * @see Module::storeAssumptionsToCheck
             */
            static void addAssumptionToCheck( const ConstraintsT& _constraints, bool _consistent, const std::string& _label );
            
            /**
             * Prints the collected assumptions in the assumption vector into _filename with an appropriate smt2 
             * header including all variables used.
             * @param _manager The manager object of this solver to store the assumptions for.
             */
            static void storeAssumptionsToCheck( const Manager& _manager );
            
            /**
             * @return true, if the module has at least one valid infeasible subset, that is all its
             *         elements are sub-formulas of the received formula (pointer must be equal).
             */
            bool hasValidInfeasibleSubset() const;
            
            /**
             * Checks the given infeasible subset for minimality by storing all subsets of it, which have a smaller size 
             * which differs from the size of the infeasible subset not more than the given threshold.
             * @param _infsubset The infeasible subset to check for minimality.
             * @param _filename The name of the file to store the infeasible subsets in order to be able to check their infeasibility.
             * @param _maxSizeDifference The maximal difference between the sizes of the subsets compared to the size of the infeasible subset.
             */
            void checkInfSubsetForMinimality( std::vector<FormulaSetT>::const_iterator _infsubset, const std::string& _filename = "smaller_muses", unsigned _maxSizeDifference = 1 ) const;
            
            /**
             * @return A pair of a Boolean and a formula, where the Boolean is true, if the received formula 
             *         could be simplified to an equisatisfiable formula. The formula is equisatisfiable to this
             *         module's reveived formula, if the Boolean is true.
             */
            virtual std::pair<bool,FormulaT> getReceivedFormulaSimplified();

        protected:

            // Internally used methods.
            /**
             * Informs the module about the given constraint. It should be tried to inform this
             * module about any constraint it could receive eventually before assertSubformula
             * is called (preferably for the first time, but at least before adding a formula
             * containing that constraint).
             * @param _constraint The constraint to inform about.
             * @return false, if it can be easily decided whether the given constraint is inconsistent;
             *          true, otherwise.
             */
            virtual bool informCore( const FormulaT& )
            {
                return true;
            }
            
            /**
             * The inverse of informing about a constraint. All data structures which were kept regarding this
             * constraint are going to be removed. Note, that this makes only sense if it is not likely enough
             * that a formula with this constraint must be solved again.
             * @param _constraint The constraint to remove from internal data structures.
             */
            virtual void deinformCore( const FormulaT& ) {}
            
            /**
             * The module has to take the given sub-formula of the received formula into account.
             *
             * @param The sub-formula to take additionally into account.
             * @return false, if it can be easily decided that this sub-formula causes a conflict with
             *          the already considered sub-formulas;
             *          true, otherwise.
             */
            virtual bool addCore( ModuleInput::const_iterator )
            {
                return true;
            }
            
            /**
             * Checks the received formula for consistency. Note, that this is an implementation of 
             * the satisfiability check of the conjunction of the so far received formulas, which does
             * actually nothing but passing the problem to its backends. This implementation is only used
             * internally and must be overwritten by any derived module.
             * @return True,    if the received formula is satisfiable;
             *         False,   if the received formula is not satisfiable;
             *         Unknown, otherwise.
             */
            virtual Answer checkCore();
            
            /**
             * Removes everything related to the given sub-formula of the received formula. However,
             * it is desired not to lose track of search spaces where no satisfying  assignment can 
             * be found for the remaining sub-formulas.
             *
             * @param The sub formula of the received formula to remove.
             */
            virtual void removeCore( ModuleInput::const_iterator ) {}
            
            /**
             * Checks for all antecedent modules and those which run in parallel with the same antecedent modules, 
             * whether one of them has determined a result.
             * @return True, if one of them has determined a result.
             */
            bool anAnswerFound() const
            {
                for( auto iter = mFoundAnswer.begin(); iter != mFoundAnswer.end(); ++iter )
                {
                    if( (*iter)->load() ) return true;
                }
                return false;
            }
            
            /**
             * Clears the assignment, if any was found
             */
            void clearModel() const
            {
				// the Assignments should not contain any values that must be deleted explicitly...
				mModel.clear();
            }

			/**
			 * Clears all assignments, if any was found
			 */
			void clearModels() const
			{
			   // the Assignments should not contain any values that must be deleted explicitly...
			   for ( Model model : mAllModels )
			   {
				   model.clear();
			   }
			   mAllModels.clear();
			}
            
            /**
             * Substitutes variable occurrences by its model value in the model values of other variables.
             */
            void cleanModel() const
            {
                mModel.clean();
            }
            
            /**
             * @return An iterator to the end of the passed formula.
             * TODO: disable this method
             */
            ModuleInput::iterator passedFormulaBegin()
            {
                return mpPassedFormula->begin();
            }
            
            /**
             * @return An iterator to the end of the passed formula.
             */
            ModuleInput::iterator passedFormulaEnd()
            {
                return mpPassedFormula->end();
            }
            
            /**
             * Adds the given set of formulas in the received formula to the origins of the given passed formula.
             * @param _formula The passed formula to set the origins for.
             * @param _origins A set of formulas in the received formula of this module.
             */
            void addOrigin( ModuleInput::iterator _formula, const FormulaT& _origin )
            {
                mpPassedFormula->addOrigin( _formula, _origin );
            }
            
            /**
             * Gets the origins of the passed formula at the given position.
             * @param _formula The position of a formula in the passed formulas.
             * @return The origins of the passed formula at the given position.
             */
            const FormulaT& getOrigins( ModuleInput::const_iterator _formula ) const
            {
                assert( _formula != mpPassedFormula->end() );
                return _formula->origins().front();
            }
            
            std::pair<ModuleInput::iterator,bool> removeOrigin( ModuleInput::iterator _formula, const FormulaT& _origin )
            {
                if( mpPassedFormula->removeOrigin( _formula, _origin ) )
                {
                    return std::make_pair( eraseSubformulaFromPassedFormula( _formula ), true );
                }
                return std::make_pair( _formula, false );
            }
            
            std::pair<ModuleInput::iterator,bool> removeOrigins( ModuleInput::iterator _formula, const std::shared_ptr<std::vector<FormulaT>>& _origins )
            {
                if( mpPassedFormula->removeOrigins( _formula, _origins ) )
                {
                    return std::make_pair( eraseSubformulaFromPassedFormula( _formula ), true );
                }
                return std::make_pair( _formula, false );
            }
            
            /**
             * Informs all backends of this module about the given constraint.
             * @param _constraint The constraint to inform about.
             */
            void informBackends( const FormulaT& _constraint )
            {
                for( Module* module : mAllBackends )
                {
                    module->inform( _constraint );
                }
            }
            
            /**
             * Adds a constraint to the collection of constraints of this module, which are informed to a 
             * freshly generated backend.
             * @param _constraint The constraint to add.
             */
           virtual void addConstraintToInform( const FormulaT& _constraint );
            
            /**
             * Copies the given sub-formula of the received formula to the passed formula. Note, that
             * there is always a link between sub-formulas of the passed formulas to sub-formulas of
             * the received formulas, which are responsible for its occurrence.
             * @param _subformula The sub-formula of the received formula to copy.
             */
            std::pair<ModuleInput::iterator,bool> addReceivedSubformulaToPassedFormula( ModuleInput::const_iterator _subformula )
            {
                assert( _subformula->formula().getType() != carl::FormulaType::AND );
                return addSubformulaToPassedFormula( _subformula->formula(), true, _subformula->formula(), nullptr, false );
            }
            
            bool originInReceivedFormula( const FormulaT& _origin ) const;
            
            /**
             * Adds the given formula to the passed formula with no origin. Note that in the next call of this module's removeSubformula, 
             * all formulas in the passed formula without origins will be removed.
             * @param _formula The formula to add to the passed formula.
             * @return A pair to the position where the formula to add has been inserted (or its first sub-formula 
             *         which has not yet been in the passed formula, in case the formula to add is a conjunction), 
             *         and a Boolean stating whether anything has been added to the passed formula.
             */
            std::pair<ModuleInput::iterator,bool> addSubformulaToPassedFormula( const FormulaT& _formula )
            {
                return addSubformulaToPassedFormula( _formula, false, FormulaT( carl::FormulaType::FALSE ), nullptr, true );
            }
            
            /**
             * Adds the given formula to the passed formula.
             * @param _formula The formula to add to the passed formula.
             * @param _origins The link of the formula to add to the passed formula to sub-formulas 
             *         of the received formulas, which are responsible for its occurrence
             * @return A pair to the position where the formula to add has been inserted (or its first sub-formula 
             *         which has not yet been in the passed formula, in case the formula to add is a conjunction), 
             *         and a Boolean stating whether anything has been added to the passed formula.
             */
            std::pair<ModuleInput::iterator,bool> addSubformulaToPassedFormula( const FormulaT& _formula, const std::shared_ptr<std::vector<FormulaT>>& _origins )
            {
                return addSubformulaToPassedFormula( _formula, false, FormulaT( carl::FormulaType::FALSE ), _origins, true );
            }
            
            /**
             * Adds the given formula to the passed formula.
             * @param _formula The formula to add to the passed formula.
             * @param _origin The sub-formula of the received formula being responsible for the
             *        occurrence of the formula to add to the passed formula.
             * @return A pair to the position where the formula to add has been inserted (or its first sub-formula 
             *         which has not yet been in the passed formula, in case the formula to add is a conjunction), 
             *         and a Boolean stating whether anything has been added to the passed formula.
             */
            std::pair<ModuleInput::iterator,bool> addSubformulaToPassedFormula( const FormulaT& _formula, const FormulaT& _origin )
            {
                return addSubformulaToPassedFormula( _formula, true, _origin, nullptr, true );
            }
            
            /**
             * Stores the trivial infeasible subset being the set of received formulas.
             */
            void generateTrivialInfeasibleSubset()
            {
                FormulaSetT infeasibleSubset;
                for( auto subformula = rReceivedFormula().begin(); subformula != rReceivedFormula().end(); ++subformula )
                    infeasibleSubset.insert( subformula->formula() );
                mInfeasibleSubsets.push_back( std::move(infeasibleSubset) );
            }
            
            /**
             * Stores an infeasible subset consisting only of the given received formula.
             */
            void receivedFormulasAsInfeasibleSubset( ModuleInput::const_iterator _subformula )
            {
                FormulaSetT infeasibleSubset;
                infeasibleSubset.insert( _subformula->formula() );
                mInfeasibleSubsets.push_back( std::move(infeasibleSubset) );
            }
            
    private:
            /**
             * This method actually implements the adding of a formula to the passed formula
             * @param _formula The formula to add to the passed formula.
             * @param _hasOrigin true, if the next argument contains the formula being the single origin.
             * @param _origin The sub-formula of the received formula being responsible for the
             *        occurrence of the formula to add to the passed formula.
             * @param _origins The link of the formula to add to the passed formula to sub-formulas 
             *         of the received formulas, which are responsible for its occurrence
             * @param _mightBeConjunction true, if the formula to add might be a conjunction.
             * @return A pair to the position where the formula to add has been inserted (or its first sub-formula 
             *         which has not yet been in the passed formula, in case the formula to add is a conjunction), 
             *         and a Boolean stating whether anything has been added to the passed formula.
             */
            std::pair<ModuleInput::iterator,bool> addSubformulaToPassedFormula( const FormulaT& _formula, bool _hasSingleOrigin, const FormulaT& _origin, const std::shared_ptr<std::vector<FormulaT>>& _origins, bool _mightBeConjunction );
    protected:
        
            /**
             * @param _origins
             * @return
             */
            std::vector<FormulaT>::const_iterator findBestOrigin( const std::vector<FormulaT>& _origins ) const;
        
            /**
             * 
             * @param _formula
             * @param _origins
             */
            void getOrigins( const FormulaT& _formula, FormulasT& _origins ) const
            {
                ModuleInput::const_iterator posInReceived = mpPassedFormula->find( _formula );
                assert( posInReceived != mpPassedFormula->end() );
                if( posInReceived->hasOrigins() )
                    collectOrigins( *findBestOrigin( posInReceived->origins() ), _origins );
            }
            
            /**
             * 
             * @param _formula
             * @param _origins
             */
            void getOrigins( const FormulaT& _formula, FormulaSetT& _origins ) const
            {
                ModuleInput::const_iterator posInReceived = mpPassedFormula->find( _formula );
                assert( posInReceived != mpPassedFormula->end() );
                if( posInReceived->hasOrigins() )
                    collectOrigins( *findBestOrigin( posInReceived->origins() ), _origins );
            }
        
            /**
             * Copies the infeasible subsets of the passed formula
             */
            void getInfeasibleSubsets();
            
            /**
             * Checks whether there is no variable assigned by both models.
             * @param _modelA The first model to check for.
             * @param _modelB The second model to check for.
             * @return true, if there is no variable assigned by both models;
             *          false, otherwise.
             */
            static bool modelsDisjoint( const Model& _modelA, const Model& _modelB );
            
            /**
             * Stores the model of a backend which determined satisfiability of the passed 
             * formula in the model of this module.
             */
            const Model& backendsModel() const;
            void getBackendsModel() const;
            
            /**
             * Stores all models of a backend in the list of all models of this module.
             */
            void getBackendsAllModels() const;

            /**
             * Runs the backend solvers on the passed formula.
             * @param _final true, if this satisfiability check will be the last one (for a global sat-check), if its result is SAT
             * @param _full false, if this module should avoid too expensive procedures and rather return unknown instead.
             * @param _objective if not set to NO_VARIABLE, the module should find an assignment minimizing this objective variable; otherwise any assignment is good.
             * @return True,    if the passed formula is consistent;
             *          False,   if the passed formula is inconsistent;
             *          Unknown, otherwise.
             */
            virtual Answer runBackends( bool _final, bool _full, carl::Variable _objective );
            virtual Answer runBackends()
            {
                return Module::runBackends( mFinalCheck, mFullCheck, mObjectiveVariable );
            }
            
            /**
             * Removes everything related to the sub-formula to remove from the passed formula in the backends of this module.
             * Afterwards the sub-formula is removed from the passed formula.
             * @param _subformula The sub-formula to remove from the passed formula.
             * @param _ignoreOrigins True, if the sub-formula shall be removed regardless of its origins (should only be applied with expertise).
             * @return 
             */
            virtual ModuleInput::iterator eraseSubformulaFromPassedFormula( ModuleInput::iterator _subformula, bool _ignoreOrigins = false );
            
            void clearPassedFormula();
            
            /**
             * Get the infeasible subsets the given backend provides. Note, that an infeasible subset
             * in a backend contains sub formulas of the passed formula and an infeasible subset of
             * this module contains sub formulas of the received formula. In this method the LATTER is
             * returned.
             * @param _backend The backend from which to obtain the infeasible subsets.
             * @return The infeasible subsets the given backend provides.
             */
            std::vector<FormulaSetT> getInfeasibleSubsets( const Module& _backend ) const;
            
            /**
             * Merges the two vectors of sets into the first one.
             *
             * ({a,b},{a,c}) and ({b,d},{b}) -> ({a,b,d},{a,b},{a,b,c,d},{a,b,c})
             *
             * @param _vecSetA  A vector of sets of constraints.
             * @param _vecSetB  A vector of sets of constraints.
             *
             * @result The vector being the two given vectors merged.
             */
            std::vector<FormulaT> merge( const std::vector<FormulaT>&, const std::vector<FormulaT>& ) const;
            
            /**
             * @param origins A vector of sets of origins.
             * @return The index of the smallest (regarding the size of the sets) element of origins
             */
            size_t determine_smallest_origin( const std::vector<FormulaT>& origins ) const;
            
            /**
             * Checks whether given the current branching value and branching variable/polynomial it is (highly) probable that
             * this branching is part of an infinite loop of branchings.
             * @param _branchingPolynomial The polynomial to branch at (in most branching strategies this is just a variable).
             * @param _branchingValue The value to branch at.
             * @return true, if this branching is probably part of an infinite loop of branchings;
             *         false, otherwise.
             */
#ifdef __VS
            bool probablyLooping( const Poly::PolyType& _branchingPolynomial, const Rational& _branchingValue ) const;
#else
            bool probablyLooping( const typename Poly::PolyType& _branchingPolynomial, const Rational& _branchingValue ) const;
#endif
            
            /**
             * Adds a lemmas which provoke a branching for the given variable at the given value,
             * if this module returns Unknown and there exists a preceding SATModule. Note that the 
             * given value is rounded down and up, if the given variable is integer-valued.
             * @param _polynomial The variable to branch for.
             * @pparam _integral A flag being true, if all variables in the polynomial to branch for are integral.
             * @param _value The value to branch at.
             * @param _premise The sub-formulas of the received formula from which the branch is followed.
             *                 Note, that a premise is not necessary, as every branch is a valid formula.
             *                 But a premise can prevent from branching unnecessarily.
             * @param _leftCaseWeak true, if a branching in the form of (or (<= p b) (> p b)) is desired.
             *                      false, if a branching in the form of (or (< p b) (>= p b)) is desired.
             * @param _preferLeftCase true, if the left case (polynomial less(or equal) 0 shall be chosen first.
             *                        false, otherwise.
             * @param _useReceivedFormulaAsPremise true, if the whole received formula should be used as premise
             */
            bool branchAt( const Poly& _polynomial, bool _integral, const Rational& _value, std::vector<FormulaT>&& _premise, bool _leftCaseWeak = true, bool _preferLeftCase = true, bool _useReceivedFormulaAsPremise = false );
            
            bool branchAt( const Poly& _polynomial, bool _integral, const Rational& _value, bool _leftCaseWeak = true, bool _preferLeftCase = true, bool _useReceivedFormulaAsPremise = false, const std::vector<FormulaT>& _premise = std::vector<FormulaT>() )
            {
                return branchAt( _polynomial, _integral, _value, std::vector<FormulaT>( _premise ), _leftCaseWeak, _preferLeftCase, _useReceivedFormulaAsPremise );
            }
            
            bool branchAt( carl::Variable::Arg _var, const Rational& _value, std::vector<FormulaT>&& _premise, bool _leftCaseWeak = true, bool _preferLeftCase = true, bool _useReceivedFormulaAsPremise = false )
            {
                return branchAt( carl::makePolynomial<Poly>( _var ), _var.type() == carl::VariableType::VT_INT, _value, std::move( _premise ), _leftCaseWeak, _preferLeftCase, _useReceivedFormulaAsPremise );
            }
            
            bool branchAt( carl::Variable::Arg _var, const Rational& _value, bool _leftCaseWeak = true, bool _preferLeftCase = true, bool _useReceivedFormulaAsPremise = false, const std::vector<FormulaT>& _premise = std::vector<FormulaT>() )
            {
                return branchAt( carl::makePolynomial<Poly>( _var ), _var.type() == carl::VariableType::VT_INT, _value, std::vector<FormulaT>( _premise ), _leftCaseWeak, _preferLeftCase, _useReceivedFormulaAsPremise );
            }
            
            template<typename P = Poly, carl::EnableIf<carl::needs_cache<P>> = carl::dummy>
            bool branchAt( const typename P::PolyType& _poly, bool _integral, const Rational& _value, std::vector<FormulaT>&& _premise, bool _leftCaseWeak = true, bool _preferLeftCase = true, bool _useReceivedFormulaAsPremise = false )
            {
                return branchAt( carl::makePolynomial<P>( _poly ), _integral, _value, std::move( _premise ), _leftCaseWeak, _preferLeftCase, _useReceivedFormulaAsPremise );
            }
            
            template<typename P = Poly, carl::EnableIf<carl::needs_cache<P>> = carl::dummy>
            bool branchAt( const typename P::PolyType& _poly, bool _integral, const Rational& _value, bool _leftCaseWeak = true, bool _preferLeftCase = true, bool _useReceivedFormulaAsPremise = false, const std::vector<FormulaT>& _premise = std::vector<FormulaT>() )
            {
                return branchAt( carl::makePolynomial<P>( _poly ), _integral, _value, std::move( std::vector<FormulaT>( _premise ) ), _leftCaseWeak, _preferLeftCase, _useReceivedFormulaAsPremise );
            }
            
            /**
             * Adds the following lemmas for the given constraint p!=0
             *
             *      (p!=0 <-> (p<0 or p>0))
             * and  not(p<0 and p>0)
             *
             * @param _unequalConstraint A constraint having the relation symbol !=.
             */
            void splitUnequalConstraint( const FormulaT& );
            
            /**
             * @return false, if the current model of this module does not satisfy the current given formula;
             *         true, if it cannot be said whether the model satisfies the given formula.
             */
            unsigned checkModel() const;

			/**
			 * Adds a formula to the InformationRelevantFormula
             * @param formula Formula to add
             */
			void addInformationRelevantFormula( const FormulaT& formula );

			/**
			 * Gets all InformationRelevantFormulas
			 * @return Set of all formulas
             */
			const std::set<FormulaT>& getInformationRelevantFormulas();

			/**
			* Checks if current lemma level is greater or equal to given level.
			* @param level Level to check.
			*/
			bool isLemmaLevel(LemmaLevel level);

        public:
            // Printing methods.
            
            /**
             * Prints everything relevant of the solver.
             * @param _out The output stream where the answer should be printed.
             * @param _initiation The line initiation.
             */
            void print( const std::string& _initiation = "***" ) const;
            
            /**
             * Prints the vector of the received formula.
             * @param _out The output stream where the answer should be printed.
             * @param _initiation The line initiation.
             */
            void printReceivedFormula( const std::string& _initiation = "***" ) const;
            
            /**
             * Prints the vector of passed formula.
             * @param _out The output stream where the answer should be printed.
             * @param _initiation The line initiation.
             */
            void printPassedFormula( const std::string& _initiation = "***" ) const;
            
            /**
             * Prints the infeasible subsets.
             * @param _out The output stream where the answer should be printed.
             * @param _initiation The line initiation.
             */
            void printInfeasibleSubsets( const std::string& _initiation = "***" ) const;
            
            /**
             * Prints the assignment of this module satisfying its received formula if it satisfiable
             * and this module could find an assignment.
             * @param _out The stream to print the assignment on.
             */
            void printModel( std::ostream& = std::cout ) const;
            
            /**
             * Prints all assignments of this module satisfying its received formula if it satisfiable
             * and this module could find an assignment.
             * @param _out The stream to print the assignment on.
             */
            void printAllModels( std::ostream& = std::cout );
        private:
            
            /**
             * Sets the solver state to the given answer value. This method also fires the flag 
             * given by the antecessor module of this module to true, if the given answer value is not Unknown.
             * @param _answer The found answer.
             */
            Answer foundAnswer( Answer _answer );
    };

	inline std::ostream& operator<<(std::ostream& os, Module::LemmaType lt) {
		switch (lt) {
			case Module::LemmaType::NORMAL: return os << "NORMAL";
			case Module::LemmaType::PERMANENT: return os << "PERMANENT";
		}
		return os << "???";
	}
}    // namespace smtrat
