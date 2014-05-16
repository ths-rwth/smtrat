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
#include <algorithm>
#include <string>
#include <chrono>
#include <atomic>
#include "ConstraintPool.h"
#include "FormulaPool.h"
#include "ValidationSettings.h"
#include "ThreadPool.h"
#include "config.h"



namespace smtrat
{
    class Manager;

    typedef std::vector<PointerSet<Formula>>           vec_set_const_pFormula;
    typedef std::map<const Formula*,vec_set_const_pFormula> FormulaOrigins;
    typedef std::vector<std::atomic_bool*>                  Conditionals;

    struct dereference_compare
    {
        template <class I>
        bool operator()(const I& a, const I& b)
        {
            return *a < *b;
        }
    };
    
    ///
    class Input : public std::list<const Formula*>
    {
        // Member.
        /// Store some properties about the conjunction of the stored formulas.
        Condition mProperties;
        
        public:
            
        Input(): 
            std::list<const Formula*>(),
            mProperties()
        {}
        
        // Methods.
        
        const Condition& properties() const
        {
            return mProperties;
        }
        
        Condition& rProperties()
        {
            return mProperties;
        }
        
        /**
         * @return true, if this formula is a conjunction of constraints;
         *          false, otherwise.
         */
        bool isConstraintConjunction() const
        {
            if( PROP_IS_PURE_CONJUNCTION <= mProperties )
                return !(PROP_CONTAINS_BOOLEAN <= mProperties);
            else
                return false;
        }

        /**
         * @return true, if this formula is a conjunction of real constraints;
         *          false, otherwise.
         */
        bool isRealConstraintConjunction() const
        {
            if( PROP_IS_PURE_CONJUNCTION <= mProperties )
                return (!(PROP_CONTAINS_INTEGER_VALUED_VARS <= mProperties) && !(PROP_CONTAINS_BOOLEAN <= mProperties));
            else
                return false;
        }

        /**
         * @return true, if this formula is a conjunction of integer constraints;
         *         false, otherwise.
         */
        bool isIntegerConstraintConjunction() const
        {
            if( PROP_IS_PURE_CONJUNCTION <= mProperties )
                return (!(PROP_CONTAINS_REAL_VALUED_VARS <= mProperties) && !(PROP_CONTAINS_BOOLEAN <= mProperties));
            else
                return false;
        }
        
        /**
         * @param _assignment The model to check conjunction of the stored formulas against.
         * @return 1, if the conjunction of the stored formulas is satisfied by the given model;
         *         0, if the given model conflicts the conjunction of the stored formulas;
         *         2, if it cannot be determined cheaply, whether the given model conflicts or satisfies 
         *            the conjunction of the stored formulas.
         */
        unsigned satisfiedBy( const Model& _assignment ) const
        {
            EvalRationalMap rationalAssigns;
            if( getRationalAssignmentsFromModel( _assignment, rationalAssigns ) )
                return satisfiedBy( rationalAssigns );
            else
                return 2; // TODO: Check also models having square roots as value.
        }
        
        /**
         * @param _assignment The assignment to check conjunction of the stored formulas against.
         * @return 1, if the conjunction of the stored formulas is satisfied by the given assignment;
         *         0, if the given assignment conflicts the conjunction of the stored formulas;
         *         2, if it cannot be determined cheaply, whether the given assignment conflicts or satisfies 
         *            the conjunction of the stored formulas.
         */
        unsigned satisfiedBy( const EvalRationalMap& _assignment ) const;
        
        /**
         * @param _subformula The formula for which to check whether it is one of the stored formulas.
         * @return true, if the given formula is one of the stored formulas;
         *         false, otherwise.
         */
        bool contains( const Formula* _subformula ) const
        {
            return std::find( begin(), end(), _subformula ) != end();
        }
        
        void updatePropositions();
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
            ///
            typedef std::chrono::high_resolution_clock clock;
            ///
            typedef std::chrono::microseconds timeunit;

        // Members.
        private:
            /// A unique ID to identify this module instance. (Could be useful but currently nowhere used)
            unsigned mId;
            /// The priority of this module to get a thread for running its check procedure.
            thread_priority mThreadPriority;
            /// The type of this module.
            ModuleType mModuleType;
        protected:
            /// Stores the infeasible subsets.
            vec_set_const_pFormula mInfeasibleSubsets;
            /// A reference to the manager.
            Manager* const mpManager;
            /// The formula passed to this module.
            const Input* mpReceivedFormula;
            /// The formula passed to the backends of this module.
            Input* mpPassedFormula;
            /// The propositions of the passed formula.
            Condition mPropositions;
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
            /// For each passed formula index its original sub formulas in the received formula.
            FormulaOrigins mPassedformulaOrigins;
            /// Stores the deductions this module or its backends made.
            std::vector<const Formula*> mDeductions;
            /// Stores the position of the first sub-formula in the passed formula, which has not yet been considered for a consistency check of the backends.
            Input::iterator mFirstSubformulaToPass;
            /// Stores the constraints which the backends must be informed about.
            std::set<const Constraint*> mConstraintsToInform;
            /// Stores the position of the first constraint of which no backend has been informed about.
            std::set<const Constraint*> mInformedConstraints;
            /// Stores the position of the first (by this module) unchecked sub-formula of the received formula.
            Input::const_iterator mFirstUncheckedReceivedSubformula;
            /// Counter used for the generation of the smt2 files to check for smaller muses.
            mutable unsigned mSmallerMusesCheckCounter;

        public:
            std::set<Input::iterator,FormulaIteratorConstraintIdCompare> mScheduledForRemoval;
            //DEPRECATED
            std::set<Input::iterator,FormulaIteratorConstraintIdCompare> mScheduledForAdding;

            Module( ModuleType type, const Input*, Conditionals&, Manager* const = NULL );
            virtual ~Module();

            static std::vector<std::string> mAssumptionToCheck;
            static std::set<std::string> mVariablesInAssumptionToCheck;

            #ifdef SMTRAT_DEVOPTION_Validation
            static ValidationSettings* validationSettings;
            #endif

            // Main interfaces
            virtual bool inform( const Constraint* const );
			virtual void init();
            virtual bool assertSubformula( Input::const_iterator );
            virtual Answer isConsistent();
            virtual void removeSubformula( Input::const_iterator );
            virtual void updateModel() const;
            virtual double rateCall( const PointerSet<Formula>& ) const;
			virtual std::list<std::vector<carl::Variable>> getModelEqualities() const;

            // Methods to read and write on the members.
            inline Answer solverState() const
            {
                return mSolverState;
            }

            inline unsigned id() const
            {
                return mId;
            }

            void setId( unsigned _id )
            {
                assert( mId == 0 && _id != 0 );
                mId = _id;
            }

            inline thread_priority threadPriority() const
            {
                return mThreadPriority;
            }

            void setThreadPriority( thread_priority _threadPriority )
            {
                mThreadPriority = _threadPriority;
            }

            inline const Input* pReceivedFormula() const
            {
                return mpReceivedFormula;
            }

            inline const Input& rReceivedFormula() const
            {
                return *mpReceivedFormula;
            }

            inline const Input* pPassedFormula() const
            {
                return mpPassedFormula;
            }

            inline const Input& rPassedFormula() const
            {
                return *mpPassedFormula;
            }

            inline const Model& model() const
            {
                return mModel;
            }
            
            inline const vec_set_const_pFormula& infeasibleSubsets() const
            {
                return mInfeasibleSubsets;
            }

            const ModuleType& type() const
            {
                return mModuleType;
            }

            const std::vector<Module*>& usedBackends() const
            {
                return mUsedBackends;
            }

            const std::set< const Constraint* >& constraintsToInform() const
            {
                return mConstraintsToInform;
            }

            const std::set< const Constraint* >& informedConstraints() const
            {
                return mInformedConstraints;
            }

            void addDeduction( const Formula* _deduction )
            {
                mDeductions.push_back( _deduction );
            }

            void clearDeductions()
            {
                mDeductions.clear();
            }

            const std::vector<const Formula*>& deductions() const
            {
                return mDeductions;
            }

            std::vector<const Formula*>& rDeductions()
            {
                return mDeductions;
            }

            Input::const_iterator firstUncheckedReceivedSubformula() const
            {
                return mFirstUncheckedReceivedSubformula;
            }

            Input::const_iterator firstSubformulaToPass() const
            {
                return mFirstSubformulaToPass;
            }

            void receivedFormulaChecked()
            {
                mFirstUncheckedReceivedSubformula = mpReceivedFormula->end();
            }

            const std::vector< std::atomic_bool* >& answerFound() const
            {
                return mFoundAnswer;
            }
            
            static const std::string moduleName( const ModuleType _moduleType )
            {
                return moduleTypeToString( _moduleType );
            }
            
            void updateDeductions();

            // Methods for debugging purposes.
            static void addAssumptionToCheck( const Formula&, bool, const std::string& );
            static void addAssumptionToCheck( const Input&, bool, const std::string& );
            static void addAssumptionToCheck( const PointerSet<Formula>&, bool, const std::string& );
            static void addAssumptionToCheck( const std::set<const Constraint*>&, bool, const std::string& );
            static void storeAssumptionsToCheck( const Manager& );
            bool hasValidInfeasibleSubset() const;
            void checkInfSubsetForMinimality( vec_set_const_pFormula::const_iterator, const std::string& = "smaller_muses", unsigned = 1 ) const;

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
            
            void setOrigins( const Formula* const _formula, vec_set_const_pFormula& _origins )
            {
                assert( mPassedformulaOrigins.find( _formula ) != mPassedformulaOrigins.end() );
                mPassedformulaOrigins[_formula] = _origins;
            }

            void addOrigin( const Formula* const _formula, const PointerSet<Formula>& _origin )
            {
                assert( mPassedformulaOrigins.find( _formula ) != mPassedformulaOrigins.end() );
                mPassedformulaOrigins[_formula].push_back( _origin );
            }

            void addOrigins( const Formula* const _formula, vec_set_const_pFormula& _origins )
            {
                assert( mPassedformulaOrigins.find( _formula ) != mPassedformulaOrigins.end() );
                vec_set_const_pFormula& formulaOrigins = mPassedformulaOrigins[_formula];
                formulaOrigins.insert( formulaOrigins.end(), _origins.begin(), _origins.end() );
            }
            
            const PointerSet<Formula>& getOrigins( Formula::const_iterator _subformula ) const
            {
                FormulaOrigins::const_iterator origins = mPassedformulaOrigins.find( *_subformula );
                assert( origins != mPassedformulaOrigins.end() );
                assert( origins->second.size() == 1 );
                return origins->second.front();
            }
            
            void getOrigins( const Formula* const _subformula, vec_set_const_pFormula& _origins ) const
            {
                FormulaOrigins::const_iterator origins = mPassedformulaOrigins.find( _subformula );
                assert( origins != mPassedformulaOrigins.end() );
                _origins = origins->second;
            }
            
            void informBackends( const Constraint* _constraint )
            {
                for( Module* module : mAllBackends )
                {
                    module->inform( _constraint );
                }
            }
            
            Answer foundAnswer( Answer );
            void addConstraintToInform( const Constraint* const _constraint );
            void addReceivedSubformulaToPassedFormula( Input::const_iterator );
            void addSubformulaToPassedFormula( const Formula*, const vec_set_const_pFormula& );
            void addSubformulaToPassedFormula( const Formula*, vec_set_const_pFormula&& );
            void addSubformulaToPassedFormula( const Formula*, const Formula* );
            void getInfeasibleSubsets();
            static bool modelsDisjoint( const Model&, const Model& );
            void getBackendsModel() const;
            Answer runBackends();
            Input::iterator removeSubformulaFromPassedFormula( Input::iterator );
            vec_set_const_pFormula getInfeasibleSubsets( const Module& ) const;
            vec_set_const_pFormula merge( const vec_set_const_pFormula&, const vec_set_const_pFormula& ) const;
            void branchAt( const Polynomial& _polynomial, const Rational& _value, const PointerSet<Formula>& = PointerSet<Formula>(), bool _leftCaseWeak = true );
            void splitUnequalConstraint( const Constraint* );
            unsigned checkModel() const;
        public:
            // Printing methods.
            void print( std::ostream& = std::cout, const std::string = "***" ) const;
            void printReceivedFormula( std::ostream& = std::cout, const std::string = "***" ) const;
            void printPassedFormula( std::ostream& = std::cout, const std::string = "***" ) const;
            void printInfeasibleSubsets( std::ostream& = std::cout, const std::string = "***" ) const;
            void printModel( std::ostream& = std::cout ) const;
        private:
            // Measuring module times.
            clock::time_point mTimerCheckStarted;
            clock::time_point mTimerAddStarted;
            clock::time_point mTimerRemoveStarted;
            timeunit mTimerAddTotal;
            timeunit mTimerCheckTotal;
            timeunit mTimerRemoveTotal;
            // For debug purposes.
            bool mTimerAddRunning;
            bool mTimerCheckRunning;
            bool mTimerRemoveRunning;
            unsigned mNrConsistencyChecks;
        public:
            void startAddTimer()
            {
                assert(!mTimerAddRunning);
                mTimerAddRunning = true;
                mTimerAddStarted = clock::now();
            }

            void stopAddTimer()
            {
                assert( mTimerAddRunning );
                mTimerAddTotal += std::chrono::duration_cast<timeunit>( clock::now() - mTimerAddStarted );
                mTimerAddRunning = false;
            }

            void startCheckTimer()
            {
                assert( !mTimerCheckRunning );
                mTimerCheckRunning = true;
                mTimerCheckStarted = clock::now();
            }

            void stopCheckTimer()
            {
                assert( mTimerCheckRunning );
                mTimerCheckTotal += std::chrono::duration_cast<timeunit>( clock::now() - mTimerCheckStarted );
                mTimerCheckRunning = false;
            }

            void startRemoveTimer()
            {
                assert( !mTimerRemoveRunning );
                mTimerRemoveRunning = true;
                mTimerRemoveStarted = clock::now();

            }

            void stopRemoveTimer()
            {
                assert( mTimerRemoveRunning );
                mTimerRemoveTotal += std::chrono::duration_cast<timeunit>( clock::now() - mTimerRemoveStarted );
                mTimerRemoveRunning = false;
            }

            void startTimers( int timers )
            {
                if( ( timers & 1 ) > 0 )
                    startAddTimer();
                if( ( timers & 2 ) > 0 )
                    startCheckTimer();
                if( ( timers & 4 ) > 0 )
                    startRemoveTimer();
            }

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

            double getAddTimerMS() const
            {
                return (double)mTimerAddTotal.count() / 1000;
            }

            double getCheckTimerMS() const
            {
                return (double)mTimerCheckTotal.count() / 1000;
            }

            double getRemoveTimerMS() const
            {
                return (double)mTimerRemoveTotal.count() / 1000;
            }

            unsigned getNrConsistencyChecks() const
            {
                return mNrConsistencyChecks;
            }
    };
}    // namespace smtrat
#endif   /* SMTRAT_MODULE_H */
