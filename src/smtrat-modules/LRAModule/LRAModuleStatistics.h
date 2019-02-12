#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <smtrat-common/statistics/Statistics.h>

namespace smtrat
{
    class LRAModuleStatistics : public Statistics
    {
    private:
        // Members.
        std::size_t mPivotingSteps = 0;
        std::size_t mCurrentPivotingSteps = 0;
        std::size_t mMostPivotingStepsInACheck = 0;
        std::size_t mChecksWithPivoting = 0;
        std::size_t mTableauxSize = 0;
        std::size_t mTableauEntries = 0;
        std::size_t mRefinements = 0;
        std::size_t mConflicts = 0;
        std::size_t mAllConflictsSizes = 0;
        std::size_t mDeductions = 0;
        std::size_t mTheoryPropagations = 0;
        std::size_t mChecks = 0;
        std::size_t mAllChecksSizes = 0;
        std::size_t mUnequalConstrainSplittings = 0;
    public:
        // Override Statistics::collect.
        void collect()
        {
           addKeyValuePair( "pivots", mPivotingSteps );
           addKeyValuePair( "max-pivots", mMostPivotingStepsInACheck );
           addKeyValuePair( "average-num-of_pivots", mChecksWithPivoting == 0 ? 0 : (double)mPivotingSteps/(double)mChecksWithPivoting );
           addKeyValuePair( "tableau-size", mTableauxSize );
           addKeyValuePair( "tableau-entries", mTableauEntries );
           addKeyValuePair( "tableau-coverage", mTableauxSize == 0 ? 0 : (double)mTableauEntries/(double)mTableauxSize );
           addKeyValuePair( "refinements", mRefinements );
           addKeyValuePair( "conflicts", mConflicts );
           addKeyValuePair( "average-conflict-size", mConflicts == 0 ? 0 : (double)mAllConflictsSizes/(double)mConflicts );
           addKeyValuePair( "lemmas", mDeductions );
           addKeyValuePair( "theory-propagations", mTheoryPropagations );
           addKeyValuePair( "checks", mChecks );
           addKeyValuePair( "checks-with-pivots", mChecksWithPivoting );
           addKeyValuePair( "average-check-size", mChecks == 0 ? 0 : (double)mAllChecksSizes/(double)mChecks );
           addKeyValuePair( "unequal-constraint-splittings", mUnequalConstrainSplittings );
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
    };
}

#endif