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
 * @version 2012-02-11
 */

#ifndef SMTRAT_MODULE_H
#define SMTRAT_MODULE_H

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
	typedef std::vector< vec_set_const_pFormula > 	  FormulaOrigins;
    /**
     * A base class for all kind of theory-solving methods
     */
    class Module
    {
        protected:
            std::vector< unsigned >     mBackTrackPoints;
            signed                      mLastBacktrackpointsEnd;
            /// Saves the infeasible subsets
            vec_set_const_pFormula      mInfeasibleSubsets;
            /// A reference to the manager
            Manager* const 		mpTSManager;
            ModuleType     		mModuleType;

        private:
            /// A vector of received constraints
            std::vector< Module* >  mUsedBackends;
            std::vector< Module* > 	mAllBackends;
            bool                    mBackendsUptodate;
            /// formula passed to this module
            const Formula*          mpReceivedFormula;
            /// formula passed to the backends
            Formula*              	mpPassedFormula;
            /// for each passed formula index its original subformulas in mpReceivedFormula
            FormulaOrigins  		mPassedFormulaOrigins;

        public:
            Module( Manager* const, const Formula* const );
            virtual ~Module();

            //Main interfaces
            virtual bool inform( const Constraint* const c )
            {
                return true;
            }

            virtual bool assertSubFormula( const Formula* const _formula );

            virtual Answer isConsistent();

            virtual void pushBacktrackPoint()
            {
				mBackTrackPoints.push_back( mLastBacktrackpointsEnd+1 );
            }

            virtual void popBacktrackPoint();

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

            inline const Formula* const receivedFormulaBack() const
            {
                return mpReceivedFormula->back();
            }

            inline const Formula* const receivedFormulaAt( unsigned _pos ) const
            {
                return mpReceivedFormula->at( _pos );
            }

            inline Formula::const_iterator receivedFormulaBegin() const
            {
                return mpReceivedFormula->begin();
            }

            inline Formula::const_iterator receivedFormulaEnd() const
            {
                return mpReceivedFormula->end();
            }

            inline bool receivedFormulaEmpty() const
            {
                return mpReceivedFormula->empty();
            }

            inline unsigned receivedFormulaSize() const
            {
                return mpReceivedFormula->size();
            }

            inline void printReceivedFormulaAlone( std::ostream& _out = std::cout, const std::string _init = "", bool _oneLine = false ) const
            {
                return mpReceivedFormula->print( _out, _init, _oneLine );
            }

            inline void passedFormulaCannotBeSolved()
            {
                mpPassedFormula->notSolvableBy( type() );
            }

            inline const Formula* passedFormulaBack() const
            {
                return mpPassedFormula->back();
            }

            inline const Formula* passedFormulaAt( unsigned _pos ) const
            {
                return mpPassedFormula->at( _pos );
            }

            inline Formula::const_iterator passedFormulaBegin() const
            {
                return mpPassedFormula->begin();
            }

            inline Formula::const_iterator passedFormulaEnd() const
            {
                return mpPassedFormula->end();
            }

            inline Formula::const_reverse_iterator passedFormulaRbegin() const
            {
                return mpPassedFormula->rbegin();
            }

            inline Formula::const_reverse_iterator passedFormulaRend() const
            {
                return mpPassedFormula->rend();
            }

            inline bool passedFormulaEmpty() const
            {
                return mpPassedFormula->empty();
            }

            inline unsigned passedFormulaSize() const
            {
                return mpPassedFormula->size();
            }

            inline void printPassedFormulaAlone( std::ostream& _out = std::cout, const std::string _init = "", bool _oneLine = false ) const
            {
                return mpPassedFormula->print( _out, _init, _oneLine );
            }

            const ModuleType type() const
            {
                return mModuleType;
            }

            signed lastBacktrackpointsEnd() const
            {
            	return mLastBacktrackpointsEnd;
            }

        //SMT
        protected:
            bool 		   addReceivedSubformulaToPassedFormula( unsigned );
            void 		   addSubformulaToPassedFormula( Formula*, vec_set_const_pFormula& );
            unsigned 		   getPositionOfReceivedFormula( const Formula* const ) const;
            unsigned 		   getPositionOfPassedFormula( const Formula* const ) const;
            void 		   setOrigins( unsigned, vec_set_const_pFormula& );
            void 		   getOrigins( const Formula* const , vec_set_const_pFormula& ) const;
            vec_set_const_pFormula merge( const vec_set_const_pFormula&, const vec_set_const_pFormula& ) const;
            Answer 		   specialCaseConsistencyCheck() const;
            vec_set_const_pFormula getInfeasibleSubsets( const Module& ) const;
            Answer 		   runBackends();
            void 		   removeSubformulaFromPassedFormula( Formula* );
            void 		   removeSubformulaFromPassedFormula( unsigned );

        private:
            void updateBackends();
            void removeAllOriginatedBy( unsigned );
            void removeAllOriginatedBy( const Formula* const );

		//Printing
	public:
            void printWithBackends( std::ostream& = std::cout, const string = "***" ) const;
            void print( std::ostream& = std::cout, const string = "***" ) const;
            void printReceivedFormula( std::ostream& = std::cout, const std::string = "***" ) const;
            void printPassedFormula( std::ostream& = std::cout, const std::string = "***" ) const;
            void printInfeasibleSubsets( std::ostream& = std::cout, const std::string = "***" ) const;
    };
}    // namespace smtrat
#endif   /* SMTRAT_MODULE_H */
