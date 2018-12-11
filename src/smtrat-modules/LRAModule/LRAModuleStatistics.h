#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <lib/utilities/stats/Statistics.h>

namespace smtrat
{
    class LRAModuleStatistics : public Statistics
    {
    private:
        // Members.
        size_t mPivotingSteps;
        size_t mCurrentPivotingSteps;
        size_t mMostPivotingStepsInACheck;
        size_t mChecksWithPivoting;
        size_t mTableauxSize;
        size_t mTableauEntries;
        size_t mRefinements;
        size_t mConflicts;
        size_t mAllConflictsSizes;
        size_t mDeductions;
        size_t mTheoryPropagations;
        size_t mChecks;
        size_t mAllChecksSizes;
        size_t mUnequalConstrainSplittings;
    public:
        // Override Statistics::collect.
        void collect()
        {
           Statistics::addKeyValuePair( "pivots", mPivotingSteps );
           Statistics::addKeyValuePair( "max-pivots", mMostPivotingStepsInACheck );
           Statistics::addKeyValuePair( "average-num-of_pivots", mChecksWithPivoting == 0 ? 0 : (double)mPivotingSteps/(double)mChecksWithPivoting );
           Statistics::addKeyValuePair( "tableau-size", mTableauxSize );
           Statistics::addKeyValuePair( "tableau-entries", mTableauEntries );
           Statistics::addKeyValuePair( "tableau-coverage", mTableauxSize == 0 ? 0 : (double)mTableauEntries/(double)mTableauxSize );
           Statistics::addKeyValuePair( "refinements", mRefinements );
           Statistics::addKeyValuePair( "conflicts", mConflicts );
           Statistics::addKeyValuePair( "average-conflict-size", mConflicts == 0 ? 0 : (double)mAllConflictsSizes/(double)mConflicts );
           Statistics::addKeyValuePair( "lemmas", mDeductions );
           Statistics::addKeyValuePair( "theory-propagations", mTheoryPropagations );
           Statistics::addKeyValuePair( "checks", mChecks );
           Statistics::addKeyValuePair( "checks-with-pivots", mChecksWithPivoting );
           Statistics::addKeyValuePair( "average-check-size", mChecks == 0 ? 0 : (double)mAllChecksSizes/(double)mChecks );
           Statistics::addKeyValuePair( "unequal-constraint-splittings", mUnequalConstrainSplittings );
        }
        
        void pivotStep()
        {
            ++mPivotingSteps;
            ++mCurrentPivotingSteps;
        }
        
        void check( const ModuleInput& _formula )
        {
            if( mCurrentPivotingSteps > 0 )
            {
                if( mCurrentPivotingSteps > mMostPivotingStepsInACheck )
                    mMostPivotingStepsInACheck = mCurrentPivotingSteps;
                ++mChecksWithPivoting;
            }
            mCurrentPivotingSteps = 0;
            ++mChecks;
            mAllChecksSizes += _formula.size();
        }
        
        void add( const ConstraintT& )
        {
        }
        
        void remove( const ConstraintT& )
        {
        }
        
        void addConflict( const std::vector<FormulaSetT>& _infSubSets )
        {
            for( auto iss = _infSubSets.begin(); iss != _infSubSets.end(); ++iss )
            {
                ++mConflicts;
                mAllConflictsSizes += iss->size();
            }
        }
        
        void addLemma()
        {
            ++mDeductions;
        }
        
        void propagateTheory()
        {
            ++mTheoryPropagations;
        }
        
        void addRefinement()
        {
            ++mRefinements;
        }
        
        void splitUnequalConstraint()
        {
            ++mUnequalConstrainSplittings;
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
            mCurrentPivotingSteps( 0 ),
            mMostPivotingStepsInACheck( 0 ),
            mChecksWithPivoting( 0 ),
            mTableauxSize( 0 ),
            mTableauEntries( 0 ),
            mRefinements( 0 ),
            mConflicts( 0 ),
            mAllConflictsSizes( 0 ),
            mDeductions( 0 ),
            mTheoryPropagations( 0 ),
            mChecks( 0 ),
            mAllChecksSizes( 0 ),
            mUnequalConstrainSplittings( 0 )
        {}
        
        ~LRAModuleStatistics() {}
    };
}

#endif