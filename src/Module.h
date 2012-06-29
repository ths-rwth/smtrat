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
 * @version 2012-06-18
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

#include "Answer.h"
#include "Formula.h"

namespace smtrat
{
    class Manager;

	typedef std::vector< std::set< const Formula* > > vec_set_const_pFormula;
	typedef std::map< const Formula*, vec_set_const_pFormula > FormulaOrigins;
    typedef std::pair< std::set< const Formula* >, const Constraint* > TheoryDeduction;
    /**
     * A base class for all kind of theory solving methods.
     */
    class Module
    {
        protected:
            /// stores the infeasible subsets
            vec_set_const_pFormula  mInfeasibleSubsets;
            /// a reference to the manager
            Manager* const          mpManager;
            ///
            ModuleType              mModuleType;
            ///
            fastConstraintSet       mConstraintsToInform;
            /// formula passed to this module
            const Formula*          mpReceivedFormula;
            /// formula passed to the backends
            Formula*              	mpPassedFormula;

        private:
            ///
            std::vector< Module* > mUsedBackends;
            ///
            std::vector< Module* > mAllBackends;
            /// for each passed formula index its original sub formulas in mpReceivedFormula
            FormulaOrigins     mPassedFormulaOrigins;
            /// stores the deductions this module or its backends made.
            std::vector< TheoryDeduction > mDeductions;
            ///
            Formula::const_iterator mFirstSubformulaToPass;
            ///
            Formula::const_iterator mFirstUncheckedReceivedSubformula;

			bool checkFirstSubformulaToPassValidity() const;

        public:
            Module( Manager* const, const Formula* const );
            virtual ~Module();

            //Main interfaces
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

            //Accessors
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

            inline const vec_set_const_pFormula& rInfeasibleSubsets() const
            {
                return mInfeasibleSubsets;
            }

            inline void passedFormulaCannotBeSolved()
            {
                mpPassedFormula->notSolvableBy( type() );
            }

            const ModuleType type() const
            {
                return mModuleType;
            }

            const std::vector< Module* >& usedBackends() const
            {
                return mUsedBackends;
            }

            const fastConstraintSet& constraintsToInform() const
            {
                return mConstraintsToInform;
            }

            void addDeduction( std::set< const Formula* > _premise, const Constraint* _conclusion )
            {
                assert( mpReceivedFormula->contains( _premise ) );
                mDeductions.push_back( TheoryDeduction( _premise, _conclusion ) );
            }

            void clearDeductions()
            {
                mDeductions.clear();
            }

            const std::vector<TheoryDeduction>& deductions() const
            {
                return mDeductions;
            }

            Formula::const_iterator firstUncheckedReceivedSubformula() const
            {
                return mFirstUncheckedReceivedSubformula;
            }

            void receivedFormulaChecked()
            {
                mFirstUncheckedReceivedSubformula = mpReceivedFormula->end();
            }

        //SMT
        protected:
			void	addReceivedSubformulaToPassedFormula( Formula::const_iterator );
            void	addSubformulaToPassedFormula( Formula*, vec_set_const_pFormula& );
			void	addSubformulaToPassedFormula( Formula* _formula, const Formula* _origin );
            void    setOrigins( const Formula* const, vec_set_const_pFormula& );
            void    getOrigins( const Formula* const , vec_set_const_pFormula& ) const;
            Answer  specialCaseConsistencyCheck() const;
            void    getInfeasibleSubsets();
            Answer  runBackends();
            Formula::iterator removeSubformulaFromPassedFormula( Formula::iterator );
            Formula::iterator pruneSubformulaFromPassedFormula( Formula::iterator );
            vec_set_const_pFormula getInfeasibleSubsets( const Module& ) const;
            vec_set_const_pFormula merge( const vec_set_const_pFormula&, const vec_set_const_pFormula& ) const;
            const vec_set_const_pFormula& getBackendsInfeasibleSubsets() const;
			const std::set<const Formula*>& getOrigins( Formula::const_iterator ) const;

        private:
            void updateDeductions();

		//Printing
        public:
            void printWithBackends( std::ostream& = std::cout, const std::string = "***" ) const;
            void print( std::ostream& = std::cout, const std::string = "***" ) const;
            void printReceivedFormula( std::ostream& = std::cout, const std::string = "***" ) const;
            void printPassedFormula( std::ostream& = std::cout, const std::string = "***" ) const;
            void printInfeasibleSubsets( std::ostream& = std::cout, const std::string = "***" ) const;
    };
}    // namespace smtrat
#endif   /* SMTRAT_MODULE_H */
