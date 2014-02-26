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


#ifndef LRAMODULESTATISTICS_H
#define	LRAMODULESTATISTICS_H

#include "../../config.h"
#ifdef SMTRAT_DEVOPTION_Statistics
#include "../../utilities/stats/Statistics.h"

namespace smtrat
{
    class LRAModuleStatistics : public Statistics
    {
    private:
        // Members.
        size_t mPivotingSteps;
        size_t mTableauxSize;
        size_t mTableauEntries;
        size_t mRefinements;
        size_t mRestarts;
        size_t mConflicts;
        size_t mAllConflictsSizes;
        size_t mDeductions;
        size_t mChecks;
        size_t mAllChecksSizes;
    public:
        // Override Statistics::collect.
        void collect()
        {
           Statistics::addKeyValuePair( "pivots", mPivotingSteps );
           Statistics::addKeyValuePair( "tableau-size", mTableauxSize );
           Statistics::addKeyValuePair( "tableau-entries", mTableauEntries );
           Statistics::addKeyValuePair( "tableau-coverage", (double)mTableauEntries/(double)mTableauxSize );
           Statistics::addKeyValuePair( "refinements", mRefinements );
           Statistics::addKeyValuePair( "restarts", mRestarts );
           Statistics::addKeyValuePair( "conflicts", mConflicts );
           Statistics::addKeyValuePair( "average-conflict-size", (double)mAllConflictsSizes/(double)mConflicts );
           Statistics::addKeyValuePair( "deductions", mDeductions );
           Statistics::addKeyValuePair( "checks", mChecks );
           Statistics::addKeyValuePair( "average-check-size", (double)mAllChecksSizes/(double)mChecks );
        }
        
        void pivotStep()
        {
            ++mPivotingSteps;
        }
        
        void setNumberOfRestarts( size_t _num )
        {
            mRestarts = _num;
        }
        
        void check( const Formula& _formula )
        {
            ++mChecks;
            mAllChecksSizes += _formula.size();
        }
        
        void add( const Constraint& )
        {
        }
        
        void remove( const Constraint& )
        {
        }
        
        void addConflict( const vec_set_const_pFormula& _infSubSets )
        {
            for( auto iss = _infSubSets.begin(); iss != _infSubSets.end(); ++iss )
            {
                ++mConflicts;
                mAllConflictsSizes += iss->size();
            }
        }
        
        void addDeduction()
        {
            ++mDeductions;
        }
        
        void addRefinement()
        {
            ++mRefinements;
        }
        
        void setTableauSize( size_t _size )
        {
            mTableauxSize = _size;
        }
        
        void setNumberOfTableauxEntries( size_t _num )
        {
            mTableauEntries = _num;
        }

        LRAModuleStatistics( const std::string& _name ) : 
            Statistics( _name, this ),
            mPivotingSteps( 0 ),
            mTableauxSize( 0 ),
            mTableauEntries( 0 ),
            mRefinements( 0 ),
            mRestarts( 0 ),
            mConflicts( 0 ),
            mAllConflictsSizes( 0 ),
            mDeductions( 0 ),
            mChecks( 0 ),
            mAllChecksSizes( 0 )
        {}
    };
}

#endif
#endif	/* LRAMODULESTATISTICS_H */