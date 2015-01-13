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
 * @file Module.h
 * @author Florian Corzilius
 * @author Ulrich Loup
 * @author Sebastian Junges
 * @since 2012-01-18
 * @version 2013-02-06
 */

#ifndef SMTRAT_MODULE_H
#define SMTRAT_MODULE_H

/// Flag activating some informative and not exaggerated output about module calls.
//#define MODULE_VERBOSE
//#define GENERATE_ONLY_PARSED_FORMULA_INTO_ASSUMPTIONS
#ifdef GENERATE_ONLY_PARSED_FORMULA_INTO_ASSUMPTIONS
#ifndef SMTRAT_DEVOPTION_Validation
#define SMTRAT_DEVOPTION_Validation
#endif
#endif


#include <vector>
#include <set>
#include <string>
#include <chrono>
#include <atomic>
#include "../modules/ModuleType.h"
#include "ModuleInput.h"
#include "ValidationSettings.h"
#include "ThreadPool.h"
#include "../config.h"



namespace smtrat
{
    class Manager;

    /// A vector of sets of formula pointers.
    typedef std::vector<std::set<FormulaT>> vec_set_const_pFormula;
    /// A vector of atomic bool pointers.
    typedef std::vector<std::atomic_bool*> Conditionals;
    
    /**
     * Stores all necessary information of an branch, which can be used to detect probable infinite loop of branchings.
     */
    struct Branching
    {
        /// The polynomial to branch at.
        Poly mPolynomial;
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
        Branching( const Poly& _polynomial, const Rational& _value ):
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
        #ifdef SMTRAT_DEVOPTION_Validation
        friend class ValidationSettings;
        #endif
        public:
            /// For time measuring purposes.
            typedef std::chrono::high_resolution_clock clock;
            /// For time measuring purposes.
            typedef std::chrono::microseconds timeunit;

        // Members.
        private:
            /// A unique ID to identify this module instance. (Could be useful but currently nowhere used)
            unsigned mId;
            /// The priority of this module to get a thread for running its check procedure.
            thread_priority mThreadPriority;
            /// The type of this module.
            ModuleType mType;
            /// The formula passed to this module.
            const ModuleInput* mpReceivedFormula;
            /// The formula passed to the backends of this module.
            ModuleInput* mpPassedFormula;
        protected:
            /// Stores the infeasible subsets.
            vec_set_const_pFormula mInfeasibleSubsets;
            /// A reference to the manager.
            Manager* const mpManager;
            /// Stores the assignment of the current satisfiable result, if existent.
            mutable Model mModel;

        private:
            /// States whether the received formula is known to be satisfiable or unsatisfiable otherwise it is set to unknown.
            Answer mSolverState;
            /// This flag is passed to any backend and if it determines an answer to a prior check call, this flag is fired.
            std::atomic_bool* mBackendsFoundAnswer;
            /// Vector of Booleans: If any of them is true, we have to terminate a running check procedure.
            Conditionals mFoundAnswer;
            /// The backends of this module which are currently used (conditions to use this module are fulfilled for the passed formula).
            std::vector<Module*> mUsedBackends;
            /// The backends of this module which have been used.
            std::vector<Module*> mAllBackends;
            /// Stores the deductions/lemmas being valid formulas this module or its backends made.
            std::vector<FormulaT> mDeductions;
            /// Stores the position of the first sub-formula in the passed formula, which has not yet been considered for a consistency check of the backends.
            ModuleInput::iterator mFirstSubformulaToPass;
            /// Stores the constraints which the backends must be informed about.
            std::set<FormulaT> mConstraintsToInform;
            /// Stores the position of the first constraint of which no backend has been informed about.
            std::set<FormulaT> mInformedConstraints;
            /// Stores the position of the first (by this module) unchecked sub-formula of the received formula.
            ModuleInput::const_iterator mFirstUncheckedReceivedSubformula;
            /// Counter used for the generation of the smt2 files to check for smaller muses.
            mutable unsigned mSmallerMusesCheckCounter;

        public:

            /**
             * Constructs a module.
             * @param type The type of this module.
             * @param _formula The formula passed to this module, called received formula.
             * @param _foundAnswer Vector of Booleans: If any of them is true, we have to terminate a running check procedure.
             * @param _manager A reference to the manager of the solver using this module.
             */
            Module( ModuleType type, const ModuleInput* _formula, Conditionals& _foundAnswer, Manager* _manager = NULL );
            
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
            /// The beginning of the cylcic buffer storing the last branches.
            static size_t mFirstPosInLastBranches;

            #ifdef SMTRAT_DEVOPTION_Validation
            /// The types of validations to involve.
            static ValidationSettings* validationSettings;
            #endif

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
            virtual bool inform( const FormulaT& );
            
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
            virtual bool assertSubformula( ModuleInput::const_iterator _subformula );
            
            /**
             * Checks the received formula for consistency. Note, that this is an implementation of 
             * the satisfiability check of the conjunction of the so far received formulas, which does
             * actually nothing but passing the problem to its backends. This implementation is only used
             * internally and must be overwritten by any derived module.
             *
             * @return True,    if the received formula is satisfiable;
             *         False,   if the received formula is not satisfiable;
             *         Unknown, otherwise.
             */
            virtual Answer isConsistent();
            
            /**
             * Removes everything related to the given sub-formula of the received formula. However,
             * it is desired not to lose track of search spaces where no satisfying  assignment can 
             * be found for the remaining sub-formulas.
             *
             * @param _subformula The sub formula of the received formula to remove.
             */
            virtual void removeSubformula( ModuleInput::const_iterator _subformula );
            
            /**
             * Updates the model, if the solver has detected the consistency of the received formula, beforehand.
             */
            virtual void updateModel() const;
            
			/**
             * Partition the variables from the current model into equivalence classes according to their assigned value.
             * 
             * The result is a set of equivalence classes of variables where all variables within one class are assigned the same value.
             * Note that the number of classes may not be minimal, i.e. two classes may actually be equivalent.
             * @return Equivalence classes.
             */
            virtual std::list<std::vector<carl::Variable>> getModelEqualities() const;

            // Methods to read and write on the members.
            /**
             * @return True, if this module is in a state, such that it has found a solution for its received formula;
             *         False, if this module is in a state, such that it has determined that there is no solution for its received formula;
             *         Unknown, otherwise.
             */
            inline Answer solverState() const
            {
                return mSolverState;
            }

            /**
             * @return A unique ID to identify this module instance.
             */
            inline unsigned id() const
            {
                return mId;
            }

            /**
             * Sets this modules unique ID to identify itself.
             * @param _id The id to set this module's id to.
             */
            void setId( unsigned _id )
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
             * @return The infeasible subsets of the set of received formulas (empty, if this module has not
             *          detected unsatisfiability of the conjunction of received formulas.
             */
            inline const vec_set_const_pFormula& infeasibleSubsets() const
            {
                return mInfeasibleSubsets;
            }

            /**
             * @return The type of this module.
             */
            const ModuleType& type() const
            {
                return mType;
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
            const std::set<FormulaT>& constraintsToInform() const
            {
                return mConstraintsToInform;
            }

            /**
             * @return The position of the first constraint of which no backend has been informed about.
             */
            const std::set<FormulaT>& informedConstraints() const
            {
                return mInformedConstraints;
            }

            /**
             * Stores a deduction/lemma being a valid formula.
             * @param _deduction The eduction/lemma to store.
             */
            void addDeduction( const FormulaT& _deduction )
            {
                mDeductions.push_back( _deduction );
            }

            /**
             * Deletes all yet found deductions/lemmas.
             */
            void clearDeductions()
            {
                mDeductions.clear();
            }

            /**
             * @return A constant reference to the deductions/lemmas being valid formulas this module or its backends made.
             */
            const std::vector<FormulaT>& deductions() const
            {
                return mDeductions;
            }

            /**
             * @return A reference to the deductions/lemmas being valid formulas this module or its backends made.
             */
            std::vector<FormulaT>& rDeductions()
            {
                return mDeductions;
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
            const std::vector< std::atomic_bool* >& answerFound() const
            {
                return mFoundAnswer;
            }
            
            /**
             * @param _moduleType The module type to return the name as string for. 
             * @return The name of the given module type as name.
             */
            static const std::string moduleName( const ModuleType _moduleType )
            {
                return moduleTypeToString( _moduleType );
            }
            
            /**
             * Stores all deductions of any backend of this module in its own deduction vector.
             */
            void updateDeductions();

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
            static void addAssumptionToCheck( const std::set<FormulaT>& _formulas, bool _consistent, const std::string& _label );
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
            static void addAssumptionToCheck( const carl::PointerSet<ConstraintT>& _constraints, bool _consistent, const std::string& _label );
            
            /**
             * Prints the collected assumptions in the assumption vector into _filename with an appropriate smt2 
             * header including all variables used.
             * @param _manager The managaer object of this solver to store the assumptions for.
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
            void checkInfSubsetForMinimality( vec_set_const_pFormula::const_iterator _infsubset, const std::string& _filename = "smaller_muses", unsigned _maxSizeDifference = 1 ) const;

        protected:

            // Internally used methods.
            
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
            void addOrigin( ModuleInput::iterator _formula, const std::set<FormulaT>& _origin )
            {
                assert( _formula != mpPassedFormula->end() );
                _formula->rOrigins().push_back( _origin );
            }

            /**
             * Adds the given sets of formulas in the received formula to the origins of the given passed formula.
             * @param _formula The passed formula to set the origins for.
             * @param _origins A vector of sets of formulas in the received formula of this module.
             */
            void addOrigins( ModuleInput::iterator _formula, vec_set_const_pFormula& _origins )
            {
                assert( _formula != mpPassedFormula->end() );
                auto& origs = _formula->rOrigins();
                origs.insert( origs.end(), _origins.begin(), _origins.end() );
            }
            
            /**
             * Gets the origins of the passed formula at the given position.
             * @param _formula The position of a formula in the passed formulas.
             * @return The origins of the passed formula at the given position.
             */
            const std::set<FormulaT>& getOrigins( ModuleInput::const_iterator _formula ) const
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
            
            std::pair<ModuleInput::iterator,bool> removeOrigins( ModuleInput::iterator _formula, const std::set<FormulaT>& _origins )
            {
                if( mpPassedFormula->removeOrigins( _formula, _origins ) )
                {
                    return std::make_pair( eraseSubformulaFromPassedFormula( _formula ), true );
                }
                return std::make_pair( _formula, false );
            }
            
            std::pair<ModuleInput::iterator,bool> removeOrigins( ModuleInput::iterator _formula, const vec_set_const_pFormula& _origins )
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
             * Sets the solver state to the given answer value. This method also fires the flag 
             * given by the antecessor module of this module to true, if the given answer value is not Unknown.
             * CALL THIS METHOD ALWAYS BEFORE RETURNING A RESULT WITH ISCONSISTENT!!!
             * @param _answer The found answer.
             */
            Answer foundAnswer( Answer _answer );
            
            /**
             * Adds a constraint to the collection of constraints of this module, which are informed to a 
             * freshly generated backend.
             * @param _constraint The constraint to add.
             */
           void addConstraintToInform( const FormulaT& _constraint );
            
            /**
             * Copies the given sub-formula of the received formula to the passed formula. Note, that
             * there is always a link between sub-formulas of the passed formulas to sub-formulas of
             * the received formulas, which are responsible for its occurrence.
             * @param _subformula The sub-formula of the received formula to copy.
             */
            std::pair<ModuleInput::iterator,bool> addReceivedSubformulaToPassedFormula( ModuleInput::const_iterator _subformula );
            
            /**
             * Adds the given formula to the passed formula.
             * @param _formula The formula to add to the passed formula.
             * @param _origins The link of the formula to add to the passed formula to sub-formulas 
             *         of the received formulas, which are responsible for its occurrence
             */
            std::pair<ModuleInput::iterator,bool> addSubformulaToPassedFormula( const FormulaT& _formula, const vec_set_const_pFormula& _origins );
            
            /**
             * Adds the given formula to the passed formula.
             * @param _formula The formula to add to the passed formula.
             * @param _origins The link of the formula to add to the passed formula to sub-formulas 
             *         of the received formulas, which are responsible for its occurrence
             */
            std::pair<ModuleInput::iterator,bool> addSubformulaToPassedFormula( const FormulaT& _formula, vec_set_const_pFormula&& _origins );
            
            /**
             * Adds the given formula to the passed formula.
             * @param _formula The formula to add to the passed formula.
             * @param _origin The sub-formula of the received formula being responsible for the
             *        occurrence of the formula to add to the passed formula.
             */
            std::pair<ModuleInput::iterator,bool> addSubformulaToPassedFormula( const FormulaT& _formula, const FormulaT& _origin );
            
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
            void getBackendsModel() const;
            
            /**
             * Runs the backend solvers on the passed formula.
             * @return True,    if the passed formula is consistent;
             *          False,   if the passed formula is inconsistent;
             *          Unknown, otherwise.
             */
            Answer runBackends();
            
            /**
             * Removes everything related to the sub-formula to remove from the passed formula in the backends of this module.
             * Afterwards the sub-formula is removed from the passed formula.
             * @param _subformula The sub-formula to remove from the passed formula.
             * @param _ignoreOrigins True, if the sub-formula shall be removed regardless of its origins (should only be applied with expertise).
             * @return 
             */
            virtual ModuleInput::iterator eraseSubformulaFromPassedFormula( ModuleInput::iterator _subformula, bool _ignoreOrigins = false );
            
            /**
             * Get the infeasible subsets the given backend provides. Note, that an infeasible subset
             * in a backend contains sub formulas of the passed formula and an infeasible subset of
             * this module contains sub formulas of the received formula. In this method the LATTER is
             * returned.
             * @param _backend The backend from which to obtain the infeasible subsets.
             * @return The infeasible subsets the given backend provides.
             */
            vec_set_const_pFormula getInfeasibleSubsets( const Module& _backend ) const;
            
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
            vec_set_const_pFormula merge( const vec_set_const_pFormula&, const vec_set_const_pFormula& ) const;
            
            /**
             * @param origins A vector of sets of origins.
             * @return The index of the smallest (regarding the size of the sets) element of origins
             */
            size_t determine_smallest_origin( std::vector<std::set<FormulaT>>& origins ) const;
            
            /**
             * Checks whether given the current branching value and branching variable/polynomial it is (highly) probable that
             * this branching is part of an infinite loop of branchings.
             * @param _branchingPolynomial The polynomial to branch at (in most branching strategies this is just a variable).
             * @param _branchingValue The value to branch at.
             * @return true, if this branching is probably part of an infinite loop of branchings;
             *         false, otherwise.
             */
            static bool probablyLooping( const Poly& _branchingPolynomial, const Rational& _branchingValue );
            
            /**
             * Adds a deductions which provoke a branching for the given variable at the given value,
             * if this module returns Unknown and there exists a preceding SATModule. Note that the 
             * given value is rounded down and up, if the given variable is integer-valued.
             * @param _var The variable to branch for.
             * @param _value The value to branch at.
             * @param _premise The sub-formulas of the received formula from which the branch is followed.
             *                 Note, that a premise is not necessary, as every branch is a valid formula.
             *                 But a premise can prevent from branching unnecessarily.
             * @param _leftCaseWeak true, if the given variable should be less or equal than the given value
             *                            or greater than the given value;
             *                      false, if the given variable should be less than the given value or
             *                             or greater or equal than the given value.
             */
            void branchAt( const Poly& _polynomial, const Rational& _value, const std::set<FormulaT>& = std::set<FormulaT>(), bool _leftCaseWeak = true );
            
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
        public:
            // Printing methods.
            
            /**
             * Prints everything relevant of the solver.
             * @param _out The output stream where the answer should be printed.
             * @param _initiation The line initiation.
             */
            void print( std::ostream& _out = std::cout, const std::string _initiation = "***" ) const;
            
            /**
             * Prints the vector of the received formula.
             * @param _out The output stream where the answer should be printed.
             * @param _initiation The line initiation.
             */
            void printReceivedFormula( std::ostream& _out = std::cout, const std::string _initiation = "***" ) const;
            
            /**
             * Prints the vector of passed formula.
             * @param _out The output stream where the answer should be printed.
             * @param _initiation The line initiation.
             */
            void printPassedFormula( std::ostream& _out = std::cout, const std::string _initiation = "***" ) const;
            
            /**
             * Prints the infeasible subsets.
             * @param _out The output stream where the answer should be printed.
             * @param _initiation The line initiation.
             */
            void printInfeasibleSubsets( std::ostream& _out = std::cout, const std::string _initiation = "***" ) const;
            
            /**
             * Prints the assignment of this module satisfying its received formula if it satisfiable
             * and this module could find an assignment.
             * @param _out The stream to print the assignment on.
             */
            void printModel( std::ostream& = std::cout ) const;
        private:
            /// Measuring module times.
            clock::time_point mTimerCheckStarted;
            /// Measuring module times.
            clock::time_point mTimerAddStarted;
            /// Measuring module times.
            clock::time_point mTimerRemoveStarted;
            /// Measuring module times.
            timeunit mTimerAddTotal;
            /// Measuring module times.
            timeunit mTimerCheckTotal;
            /// Measuring module times.
            timeunit mTimerRemoveTotal;
            /// For debug purposes.
            bool mTimerAddRunning;
            /// For debug purposes.
            bool mTimerCheckRunning;
            /// For debug purposes.
            bool mTimerRemoveRunning;
            /// For debug purposes.
            unsigned mNrConsistencyChecks;
        public:
            /**
             * Starts the timer to stop the timing for adding formulas performed by this module.
             */
            void startAddTimer()
            {
                assert(!mTimerAddRunning);
                mTimerAddRunning = true;
                mTimerAddStarted = clock::now();
            }

            /**
             * Stops the timer to stop the timing for adding formulas performed by this module.
             */
            void stopAddTimer()
            {
                assert( mTimerAddRunning );
                mTimerAddTotal += std::chrono::duration_cast<timeunit>( clock::now() - mTimerAddStarted );
                mTimerAddRunning = false;
            }

            /**
             * Starts the timer to stop the timing for checking formulas performed by this module.
             */
            void startCheckTimer()
            {
                assert( !mTimerCheckRunning );
                mTimerCheckRunning = true;
                mTimerCheckStarted = clock::now();
            }

            /**
             * Stops the timer to stop the timing for checking formulas performed by this module.
             */
            void stopCheckTimer()
            {
                assert( mTimerCheckRunning );
                mTimerCheckTotal += std::chrono::duration_cast<timeunit>( clock::now() - mTimerCheckStarted );
                mTimerCheckRunning = false;
            }

            /**
             * Starts the timer to stop the timing for removing formulas performed by this module.
             */
            void startRemoveTimer()
            {
                assert( !mTimerRemoveRunning );
                mTimerRemoveRunning = true;
                mTimerRemoveStarted = clock::now();

            }

            /**
             * Stops the timer to stop the timing for removing formulas performed by this module.
             */
            void stopRemoveTimer()
            {
                assert( mTimerRemoveRunning );
                mTimerRemoveTotal += std::chrono::duration_cast<timeunit>( clock::now() - mTimerRemoveStarted );
                mTimerRemoveRunning = false;
            }

            /**
             * Starts the timers according to the given integer of this module:
             *      If its first bit is set, the timer for adding formulas is started.
             *      If its second bit is set, the timer for checking formulas is started.
             *      If its third bit is set, the timer for removing formulas is started.
             * @param timers The integer specifying which timers to start.
             */
            void startTimers( int timers )
            {
                if( ( timers & 1 ) > 0 )
                    startAddTimer();
                if( ( timers & 2 ) > 0 )
                    startCheckTimer();
                if( ( timers & 4 ) > 0 )
                    startRemoveTimer();
            }

            /**
             * Stops all timers of this module.
             * @return An integer showing which timers were stopped:
             *      If its first bit is set, the timer for adding formulas was stopped.
             *      If its second bit is set, the timer for checking formulas was stopped.
             *      If its third bit is set, the timer for removing formulas was stopped.
             */
            int stopAllTimers()
            {
                int result = 0;
                if( mTimerAddRunning )
                {
                    stopAddTimer();
                    result |= 1;
                }
                if( mTimerCheckRunning )
                {
                    stopCheckTimer();
                    result |= 2;
                }
                if( mTimerRemoveRunning )
                {
                    stopRemoveTimer();
                    result |= 4;
                }
                return result;
            }

            /**
             * @return The total time of adding formulas performed by this module.
             */
            double getAddTimerMS() const
            {
                return (double)mTimerAddTotal.count() / 1000;
            }

            /**
             * @return The total time of checking formulas performed by this module.
             */
            double getCheckTimerMS() const
            {
                return (double)mTimerCheckTotal.count() / 1000;
            }

            /**
             * @return The total time of removing formulas performed by this module.
             */
            double getRemoveTimerMS() const
            {
                return (double)mTimerRemoveTotal.count() / 1000;
            }

            /**
             * @return The number of consistency checks performed by this module.
             */
            unsigned getNrConsistencyChecks() const
            {
                return mNrConsistencyChecks;
            }
    };
}    // namespace smtrat
#endif   /* SMTRAT_MODULE_H */
