/** 
 * @file   VSStatistics.h
 * @author: Florian Corzilius
 *
 * 
 */

#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <smtrat-common/statistics/Statistics.h>

namespace smtrat
{
    class VSStatistics : public Statistics
    {
    private:
        // Members.
        carl::uint mChecks = 0;
        carl::uint mConflicts = 0;
        carl::uint mCoveringSets = 0;
        double mCoveringSetSavings = 0;
        double mInfSubsetsSavings = 0;
        carl::uint mCreatedTCs = 0;
        carl::uint mConsideredStates = 0;
        carl::uint mConsideredCases = 0;
        carl::uint mLocalConflicts = 0;
        carl::uint mLCOmittedConstraints = 0;
        carl::uint mVBOmittedConstraints = 0;
        carl::uint mBackjumpings = 0;
        carl::uint mBJOmittedConstraints = 0;
        carl::uint mVBOmittedTCs = 0;
        carl::uint mBranchingLemmas = 0;

    public:
        VSStatistics( const std::string& _name ) : 
            Statistics( _name )
        {}

        ~VSStatistics() {}

        void collect()
        {
            addKeyValuePair( "check-calls", mChecks );
            addKeyValuePair( "created-test-candidates", mCreatedTCs );
            addKeyValuePair( "considered-states", mConsideredStates );
            addKeyValuePair( "considered-cases", mConsideredCases );
            addKeyValuePair( "omitted-test-candidates-by-variable-bounds", mVBOmittedTCs );
            addKeyValuePair( "omitted-constraints-by-variable-bounds", mVBOmittedConstraints );
            addKeyValuePair( "created-covering-sets", mCoveringSets );
            addKeyValuePair( "average-covering-set-gain", mCoveringSets == 0 ? 0 : (mCoveringSetSavings/(double)mCoveringSets) );
            addKeyValuePair( "average-infeasible-subset-gain", mConflicts == 0 ? 0 : (mInfSubsetsSavings/(double)mConflicts) );
            addKeyValuePair( "local-conflicts", mLocalConflicts );
            addKeyValuePair( "omitted-constraints-by-local-conflicts", mLCOmittedConstraints );
            addKeyValuePair( "backjumpings", mBackjumpings );
            addKeyValuePair( "omitted-constraints-by-backjumping", mBJOmittedConstraints );
            addKeyValuePair( "branching-lemmas", mBranchingLemmas );
        }
        
        void check()
        {
            ++mChecks;
        }
        
		template<typename ModuleInput>
        void addConflict( const ModuleInput& _formula, const std::vector<FormulaSetT>& _infSubSets )
        {
            assert( !_formula.empty() );
            for( const auto& iss : _infSubSets )
            {
                ++mConflicts;
                mInfSubsetsSavings += (double)(_formula.size()-iss.size())/(double)_formula.size();
            }
        }

        void branch()
        {
            ++mBranchingLemmas;
        }
        
        void createTestCandidate()
        {
            ++mCreatedTCs;
        }
        
        void omittedConstraintByVB( carl::uint _numberOfOmittedConstraints = 1 )
        {
            mVBOmittedConstraints += _numberOfOmittedConstraints;
        }
        
        void localConflict( carl::uint _numberOfOmittedConstraints )
        {
            mBranchingLemmas += _numberOfOmittedConstraints;
            ++mLocalConflicts;
        }
        
        void backjumping( carl::uint _numberOfOmittedConstraints )
        {
            ++mBackjumpings;
            mBJOmittedConstraints += _numberOfOmittedConstraints;
        }
        
        void coveringSet( carl::uint _coveringSetSize, carl::uint _numberOfConstraintsToSolve )
        {
            ++mCoveringSets;
            if( _numberOfConstraintsToSolve > 0 )
                mCoveringSetSavings += (double)(_numberOfConstraintsToSolve-_coveringSetSize)/(double)_numberOfConstraintsToSolve;
        }
        
        void considerState()
        {
            ++mConsideredStates;
        }
        
        void considerCase()
        {
            ++mConsideredCases;
        }
        
        void omittedConstraintsWithVB( carl::uint _numberOfOmittedConstraints = 1 )
        {
            mVBOmittedConstraints += _numberOfOmittedConstraints;
        }
        
        void omittedTestCandidateWithVB(  carl::uint _numberOfOmittedConstraints )
        {
            ++mVBOmittedTCs;
            mVBOmittedConstraints += _numberOfOmittedConstraints;
        }
    };

}
#endif
