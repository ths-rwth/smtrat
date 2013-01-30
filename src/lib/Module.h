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
 * @version 2013-01-16
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

#include "Answer.h"
#include "Formula.h"
#include "ValidationSettings.h"
#include "config.h"


namespace smtrat
{
    class Manager;

    typedef std::vector<std::set<const Formula*> >           vec_set_const_pFormula;
    typedef std::map<const Formula*, vec_set_const_pFormula> FormulaOrigins;

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
        #ifdef SMTRAT_ENABLE_VALIDATION
        friend class ValidationSettings;
        #endif
        public:
            typedef std::map< const std::string, std::string > Model;
            typedef std::chrono::high_resolution_clock clock;
            typedef std::chrono::microseconds timeunit; 
            
        protected:
            ///
            Answer mSolverState;
            ///
            unsigned mId;
            /// stores the infeasible subsets
            vec_set_const_pFormula mInfeasibleSubsets;
            /// a reference to the manager
            Manager* const mpManager;
            ///
            ModuleType mModuleType;
            ///
            fastConstraintSet mConstraintsToInform;
            /// formula passed to this module
            const Formula* mpReceivedFormula;
            /// formula passed to the backends
            Formula* mpPassedFormula;
            ///
            Model mModel;

        private:
            ///
            std::vector<Module*> mUsedBackends;
            ///
            std::vector<Module*> mAllBackends;
            /// for each passed formula index its original sub formulas in mpReceivedFormula
            FormulaOrigins mPassedformulaOrigins;
            /// stores the deductions this module or its backends made.
            std::vector<Formula*> mDeductions;
            ///
            Formula::iterator mFirstSubformulaToPass;
            ///
            Formula::const_iterator mFirstUncheckedReceivedSubformula;
            /// Counter used for the generation of the smt2 files to check for smaller muses.
            mutable unsigned mSmallerMusesCheckCounter;

            // 
            std::set<Formula::iterator, dereference_compare> mScheduledForRemoval;
            
            
            bool checkFirstSubformulaToPassValidity() const;

        public:
            Module( ModuleType type, const Formula* const, Manager* const = NULL );
            virtual ~Module();

            static std::vector<std::string> mAssumptionToCheck;
            static std::set<std::string> mVariablesInAssumptionToCheck;
            
            #ifdef SMTRAT_ENABLE_VALIDATION
            static ValidationSettings* validationSettings;
            #endif

            // Main interfaces
            virtual bool inform( const Constraint* const _constraint )
            {
                mConstraintsToInform.insert( _constraint );
                return true;
            }
            virtual bool assertSubformula( Formula::const_iterator _subformula )
            {
                if( mFirstUncheckedReceivedSubformula == mpReceivedFormula->end() )
                {
                    mFirstUncheckedReceivedSubformula = _subformula;
                }
                return true;
            }
            virtual Answer isConsistent();
            virtual void removeSubformula( Formula::const_iterator );
            virtual void updateModel();

            // Accessors
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

            inline void passedFormulaCannotBeSolved()
            {
                //TODO do we need this???
                //mpPassedFormula->notSolvableBy( type() );
            }

            const ModuleType type() const
            {
                return mModuleType;
            }

            const std::vector<Module*>& usedBackends() const
            {
                return mUsedBackends;
            }

            const fastConstraintSet& constraintsToInform() const
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

            static void addAssumptionToCheck( const Formula&, bool, const std::string );
            static void addAssumptionToCheck( const std::set<const Formula*>&, bool, const std::string );
            static void addAssumptionToCheck( const std::set<const Constraint*>&, bool, const std::string );
            static void storeAssumptionsToCheck( const Manager& );
            static const std::string moduleName( const ModuleType );
            //SMT
            void storeSmallerInfeasibleSubsetsCheck(const std::vector<Formula> &, const std::string= "smaller_muses") const;
            std::vector<Formula> generateSubformulaeOfInfeasibleSubset( unsigned infeasiblesubset, unsigned size ) const;
            void updateDeductions();
        protected:
            void addReceivedSubformulaToPassedFormula( Formula::const_iterator );
            void addSubformulaToPassedFormula( Formula*, const vec_set_const_pFormula& );
            void addSubformulaToPassedFormula( Formula*, const Formula* );
            void setOrigins( const Formula* const , vec_set_const_pFormula& );
            void getOrigins( const Formula* const , vec_set_const_pFormula& ) const;
            Answer specialCaseConsistencyCheck() const;
            void getInfeasibleSubsets();
            static bool modelsDisjoint( const Model&, const Model& );
            void getBackendsModel();
            Answer runBackends();
            Formula::iterator removeSubformulaFromPassedFormula( Formula::iterator, bool involveBackends = true );
            void scheduleSubformulaForRemovalFromPassedFormula( Formula::iterator );
            void removeScheduled();
            Formula::iterator pruneSubformulaFromPassedFormula( Formula::iterator );
            vec_set_const_pFormula getInfeasibleSubsets( const Module& ) const;
            vec_set_const_pFormula merge( const vec_set_const_pFormula&, const vec_set_const_pFormula& ) const;
            const vec_set_const_pFormula& getBackendsInfeasibleSubsets() const;
            const std::set<const Formula*>& getOrigins( Formula::const_iterator ) const;
            //
            // Print methods
            //
        public:
            void print( std::ostream& = std::cout, const std::string = "***" ) const;
            void printReceivedFormula( std::ostream& = std::cout, const std::string = "***" ) const;
            void printPassedFormula( std::ostream& = std::cout, const std::string = "***" ) const;
            void printInfeasibleSubsets( std::ostream& = std::cout, const std::string = "***" ) const;
        
            //
            // Measuring module times
            //
        private:
            clock::time_point mTimerCheckStarted;
            clock::time_point mTimerAddStarted;
            clock::time_point mTimerRemoveStarted;
            timeunit mTimerAddTotal;
            timeunit mTimerCheckTotal;
            timeunit mTimerRemoveTotal;
            // for debug purposes
            bool mTimerAddRunning;
            bool mTimerCheckRunning;
            bool mTimerRemoveRunning;
        public:
            void startCheckTimer();
            void stopCheckTimer();
            void startAddTimer();
            void stopAddTimer();
            void startRemoveTimer();
            void stopRemoveTimer();
            int stopAllTimers();
            void startTimers(int timers);
        public:
            double getAddTimerMS() const;
            double getCheckTimerMS() const;
            double getRemoveTimerMS() const;
            
    };
}    // namespace smtrat
#endif   /* SMTRAT_MODULE_H */
