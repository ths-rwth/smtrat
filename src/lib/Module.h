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
        #ifdef SMTRAT_DEVOPTION_Validation
        friend class ValidationSettings;
        #endif
        public:
            /// Data type for a assignment assigning a variable, represented as a string, a real algebraic number, represented as a string.
            typedef std::map< const std::string, std::string > Model;
            ///
            typedef std::chrono::high_resolution_clock clock;
            ///
            typedef std::chrono::microseconds timeunit;

        /*
         * Members:
         */
        protected:
            /// States whether the received formula is known to be satisfiable or unsatisfiable otherwise it is set to unknown.
            Answer mSolverState;
            /// A unique ID to identify this module instance. (Could be useful but currently nowhere used)
            unsigned mId;
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
            /// Stores the assignment of the current satisfiable result, if existent.
            Model mModel;

        private:
            ///
            bool mBackendFoundAnswer;
            ///
            bool& mFoundAnswer;
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

        /*
         * Methods:
         */

            bool checkFirstSubformulaToPassValidity() const;

        public:

            //DEPRECATED
            std::set<Formula::iterator, FormulaIteratorConstraintIdCompare> mScheduledForRemoval;
            //DEPRECATED
            std::set<Formula::iterator, FormulaIteratorConstraintIdCompare> mScheduledForAdding;

            Module( ModuleType type, const Formula* const, bool&, Manager* const = NULL );
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

            const ModuleType type() const
            {
                return mModuleType;
            }

            const std::vector<Module*>& usedBackends() const
            {
                return mUsedBackends;
            }

            const std::list<const Constraint* >& constraintsToInform() const
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

            static void addAssumptionToCheck( const Formula&, bool, const std::string& );
            static void addAssumptionToCheck( const std::set<const Formula*>&, bool, const std::string& );
            static void addAssumptionToCheck( const std::set<const Constraint*>&, bool, const std::string& );
            static void storeAssumptionsToCheck( const Manager& );
            static const std::string moduleName( const ModuleType );
            void storeSmallerInfeasibleSubsetsCheck(const std::vector<Formula> &, const std::string& = "smaller_muses") const;
            std::vector<Formula> generateSubformulaeOfInfeasibleSubset( unsigned infeasiblesubset, unsigned size ) const;
            void updateDeductions();
        protected:
            void addConstraintToInform( const Constraint* const _constraint );
            void addReceivedSubformulaToPassedFormula( Formula::const_iterator );
            void addSubformulaToPassedFormula( Formula*, const vec_set_const_pFormula& );
            void addSubformulaToPassedFormula( Formula*, const Formula* );
            void setOrigins( const Formula* const, vec_set_const_pFormula& );
            void addOrigin( const Formula* const, std::set< const Formula* >& );
            void addOrigins( const Formula* const, vec_set_const_pFormula& );
            void getOrigins( const Formula* const, vec_set_const_pFormula& ) const;
            Answer specialCaseConsistencyCheck() const;
            void getInfeasibleSubsets();
            static bool modelsDisjoint( const Model&, const Model& );
            void getBackendsModel();
            Answer runBackends();
            void clearReceivedFormula( Formula::const_iterator _received, Formula::iterator _passed );
            Formula::iterator removeSubformulaFromPassedFormula( Formula::iterator, bool local = false, bool forceBackendCall = false );
            Formula::iterator pruneSubformulaFromPassedFormula( Formula::iterator );
            vec_set_const_pFormula getInfeasibleSubsets( const Module& ) const;
            vec_set_const_pFormula merge( const vec_set_const_pFormula&, const vec_set_const_pFormula& ) const;
            const vec_set_const_pFormula& getBackendsInfeasibleSubsets() const;
            const std::set<const Formula*>& getOrigins( Formula::const_iterator ) const;
            /*
             * Printing methods:
             */
        public:
            void print( std::ostream& = std::cout, const std::string = "***" ) const;
            void printReceivedFormula( std::ostream& = std::cout, const std::string = "***" ) const;
            void printPassedFormula( std::ostream& = std::cout, const std::string = "***" ) const;
            void printInfeasibleSubsets( std::ostream& = std::cout, const std::string = "***" ) const;

            /*
             * Measuring module times:
             */
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
            unsigned mNrConsistencyChecks;
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
            unsigned getNrConsistencyChecks() const;

    };
}    // namespace smtrat
#endif   /* SMTRAT_MODULE_H */
