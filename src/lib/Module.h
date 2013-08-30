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


#include <vector>
#include <map>
#include <set>
#include <algorithm>
#include <string>
#include <ginac/ginac.h>
#include <chrono>
#include <atomic>

#include "Answer.h"
#include "Formula.h"
#include "ValidationSettings.h"
#include "ThreadPool.h"
#include "config.h"


namespace smtrat
{
    class Manager;

    typedef std::vector<std::set<const Formula*> >           vec_set_const_pFormula;
    typedef std::map<const Formula*, vec_set_const_pFormula> FormulaOrigins;
    typedef std::vector< std::atomic_bool* >                 Conditionals;

    struct dereference_compare {
        template <class I>
        bool operator()(const I& a, const I& b) {
            return *a < *b;
        }
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
            /// Data type for storing the domain and the value of an assignment.
            typedef struct
            {
                Variable_Domain domain;
                union
                {
                    ex*  theoryValue;
                    bool booleanValue;
                };
            } Assignment;
            /// Data type for a assignment assigning a variable, represented as a string, a real algebraic number, represented as a string.
            typedef std::map< const std::string, Assignment* > Model;
            ///
            typedef std::chrono::high_resolution_clock clock;
            ///
            typedef std::chrono::microseconds timeunit;

        /*
         * Members:
         */
        protected:
            /// A unique ID to identify this module instance. (Could be useful but currently nowhere used)
            unsigned mId;
            /// The priority of this module to get a thread for running its check procedure.
            thread_priority mThreadPriority;
            /// Stores the infeasible subsets.
            vec_set_const_pFormula mInfeasibleSubsets;
            /// A reference to the manager.
            Manager* const mpManager;
            /// The type of this module.
            ModuleType mModuleType;
            /// The formula passed to this module.
            const Formula* mpReceivedFormula;
            /// The formula passed to the backends of this module.
            Formula* mpPassedFormula;

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
            std::vector<Formula*> mDeductions;
            /// Stores the position of the first sub-formula in the passed formula, which has not yet been considered for a consistency check of the backends.
            Formula::iterator mFirstSubformulaToPass;
            /// Stores the constraints which the backends must be informed about.
            std::list<const Constraint* > mConstraintsToInform;
            /// Stores the position of the first constraint of which no backend has been informed about.
            std::list<const Constraint* >::iterator mFirstConstraintToInform;
            /// Stores the position of the first (by this module) unchecked sub-formula of the received formula.
            Formula::const_iterator mFirstUncheckedReceivedSubformula;
            /// Counter used for the generation of the smt2 files to check for smaller muses.
            mutable unsigned mSmallerMusesCheckCounter;
            /// Stores the assignment of the current satisfiable result, if existent.
            Model mModel;

        public:
            std::set<Formula::iterator, FormulaIteratorConstraintIdCompare> mScheduledForRemoval;
            //DEPRECATED
            std::set<Formula::iterator, FormulaIteratorConstraintIdCompare> mScheduledForAdding;

            Module( ModuleType type, const Formula* const, Conditionals&, Manager* const = NULL );
            virtual ~Module();

            static std::vector<std::string> mAssumptionToCheck;
            static std::set<std::string> mVariablesInAssumptionToCheck;

            #ifdef SMTRAT_DEVOPTION_Validation
            static ValidationSettings* validationSettings;
            #endif

            // Main interfaces
            virtual bool inform( const Constraint* const );
            virtual bool assertSubformula( Formula::const_iterator );
            virtual Answer isConsistent();
            virtual void removeSubformula( Formula::const_iterator );
            virtual void updateModel();

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

            inline const Formula* const pReceivedFormula() const
            {
                return mpReceivedFormula;
            }

            inline const Formula& rReceivedFormula() const
            {
                return *mpReceivedFormula;
            }

            inline const Formula* const pPassedFormula() const
            {
                return mpPassedFormula;
            }

            inline const Formula& rPassedFormula() const
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

            const ModuleType type() const
            {
                return mModuleType;
            }

            const std::vector<Module*>& usedBackends() const
            {
                return mUsedBackends;
            }

            const std::list< const Constraint* >& constraintsToInform() const
            {
                return mConstraintsToInform;
            }

            void addDeduction( Formula* _deduction )
            {
                mDeductions.push_back( _deduction );
            }

            void clearDeductions()
            {
                while( !mDeductions.empty() )
                {
                    Formula* toDelete = mDeductions.back();
                    mDeductions.pop_back();
                    delete toDelete;
                }
            }

            const std::vector<Formula*>& deductions() const
            {
                return mDeductions;
            }

            std::vector<Formula*>& rDeductions()
            {
                return mDeductions;
            }

            Formula::const_iterator firstUncheckedReceivedSubformula() const
            {
                return mFirstUncheckedReceivedSubformula;
            }

            Formula::const_iterator firstSubformulaToPass() const
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
            
            const std::string moduleName( const ModuleType _moduleType ) const
            {
                return moduleTypeToString( _moduleType );
            }
            
            void updateDeductions();

            // Methods for debugging purposes.
            static void addAssumptionToCheck( const Formula&, bool, const std::string& );
            static void addAssumptionToCheck( const std::set<const Formula*>&, bool, const std::string& );
            static void addAssumptionToCheck( const std::set<const Constraint*>&, bool, const std::string& );
            static void storeAssumptionsToCheck( const Manager& );
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
            void clearModel()
            {
                while( !mModel.empty() )
                {
                    Assignment* assToDel = mModel.begin()->second;
                    if( assToDel->domain != BOOLEAN_DOMAIN )
                    {
                        ex* exToDel = assToDel->theoryValue;
                        delete assToDel;
                        delete exToDel;
                    }
                    mModel.erase( mModel.begin() );
                }
            }
            
            /**
             * Extends the model by the assignment of the given variable to the given value.
             * 
             * @param _varName The name of the variable for which we want to add an assignment.
             * @param _assignment The value and the domain of the assignment.
             * @return true, if the assignment could be successfully added;
             *          false, if the given variable is already assigned to a value by the model of this module.
             */
            bool extendModel( const std::string& _varName, Assignment* _assignment )
            {
                if( _assignment->domain != BOOLEAN_DOMAIN )
                {
                    std::string extName = Formula::constraintPool().externalName( _varName );
                    if( extName.substr( 0, Formula::constraintPool().externalVarNamePrefix().size() ) != Formula::constraintPool().externalVarNamePrefix() )
                    {
                        return mModel.insert( pair< const string, Assignment* >( _varName, _assignment ) ).second;
                    }
                    return false;
                }
                else
                {
                    if( _varName.substr( 0, Formula::constraintPool().externalVarNamePrefix().size() ) != Formula::constraintPool().externalVarNamePrefix() )
                    {
                        return mModel.insert( pair< const string, Assignment* >( _varName, _assignment ) ).second;
                    }
                    return false;
                }
            }
            
            void setOrigins( const Formula* const _formula, vec_set_const_pFormula& _origins )
            {
                assert( mPassedformulaOrigins.find( _formula ) != mPassedformulaOrigins.end() );
                mPassedformulaOrigins[_formula] = _origins;
            }

            void addOrigin( const Formula* const _formula, set< const Formula* >& _origin )
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
            
            const std::set<const Formula*>& getOrigins( Formula::const_iterator _subformula ) const
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

            Answer foundAnswer( Answer );
            void addConstraintToInform( const Constraint* const _constraint );
            void addReceivedSubformulaToPassedFormula( Formula::const_iterator );
            void addSubformulaToPassedFormula( Formula*, const vec_set_const_pFormula& );
            void addSubformulaToPassedFormula( Formula*, const Formula* );
            void getInfeasibleSubsets();
            static bool modelsDisjoint( const Model&, const Model& );
            void getBackendsModel();
            Answer runBackends();
            Formula::iterator removeSubformulaFromPassedFormula( Formula::iterator );
            vec_set_const_pFormula getInfeasibleSubsets( const Module& ) const;
            vec_set_const_pFormula merge( const vec_set_const_pFormula&, const vec_set_const_pFormula& ) const;
            const vec_set_const_pFormula& getBackendsInfeasibleSubsets() const;
        public:
            // Printing methods.
            void print( std::ostream& = std::cout, const std::string = "***" ) const;
            void printReceivedFormula( std::ostream& = std::cout, const std::string = "***" ) const;
            void printPassedFormula( std::ostream& = std::cout, const std::string = "***" ) const;
            void printInfeasibleSubsets( std::ostream& = std::cout, const std::string = "***" ) const;
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
                return mTimerAddTotal.count() / 1000;
            }

            double getCheckTimerMS() const
            {
                return mTimerCheckTotal.count() / 1000;
            }

            double getRemoveTimerMS() const
            {
                return mTimerRemoveTotal.count() / 1000;
            }

            unsigned getNrConsistencyChecks() const
            {
                return mNrConsistencyChecks;
            }
    };
}    // namespace smtrat
#endif   /* SMTRAT_MODULE_H */
