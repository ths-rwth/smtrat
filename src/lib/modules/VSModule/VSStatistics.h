/** 
 * @file   VSStatistics.h
 * @author: Florian Corzilius
 *
 * 
 */

#pragma once

#ifdef SMTRAT_DEVOPTION_Statistics
#include "../../config.h"
#include "../../utilities/stats/Statistics.h"

namespace smtrat
{
    class VSStatistics : public Statistics
    {
    private:
        // Members.
        carl::uint mChecks;
        carl::uint mConflicts;
        carl::uint mCoveringSets;
        double mCoveringSetSavings;
        double mInfSubsetsSavings;
        carl::uint mCreatedTCs;
        carl::uint mConsideredStates;
        carl::uint mConsideredCases;
        carl::uint mLocalConflicts;
        carl::uint mLCOmittedConstraints;
        carl::uint mVBOmittedConstraints;
        carl::uint mBackjumpings;
        carl::uint mBJOmittedConstraints;
        carl::uint mVBOmittedTCs;
        carl::uint mBranchingLemmas;

    public:
        VSStatistics( const std::string& _name ) : 
            Statistics( _name, this ),
            mChecks( 0 ),
            mConflicts( 0 ),
            mCoveringSets( 0 ),
            mCoveringSetSavings( 0.0 ),
            mInfSubsetsSavings( 0.0 ),
            mCreatedTCs( 0 ),
            mConsideredStates( 0 ),
            mConsideredCases( 0 ),
            mLocalConflicts( 0 ),
            mLCOmittedConstraints( 0 ),
            mVBOmittedConstraints( 0 ),
            mBackjumpings( 0 ),
            mBJOmittedConstraints( 0 ),
            mVBOmittedTCs( 0 ),
            mBranchingLemmas( 0 )
        {}

        ~VSStatistics() {}

        void collect()
        {
            Statistics::addKeyValuePair( "check-calls", mChecks );
            Statistics::addKeyValuePair( "created-test-candidates", mCreatedTCs );
            Statistics::addKeyValuePair( "considered-states", mConsideredStates );
            Statistics::addKeyValuePair( "considered-cases", mConsideredCases );
            Statistics::addKeyValuePair( "omitted-test-candidates-by-variable-bounds", mVBOmittedTCs );
            Statistics::addKeyValuePair( "omitted-constraints-by-variable-bounds", mVBOmittedConstraints );
            Statistics::addKeyValuePair( "created-covering-sets", mCoveringSets );
            Statistics::addKeyValuePair( "average-covering-set-gain", mCoveringSets == 0 ? 0 : (mCoveringSetSavings/(double)mCoveringSets) );
            Statistics::addKeyValuePair( "average-infeasible-subset-gain", mConflicts == 0 ? 0 : (mInfSubsetsSavings/(double)mConflicts) );
            Statistics::addKeyValuePair( "local-conflicts", mLocalConflicts );
            Statistics::addKeyValuePair( "omitted-constraints-by-local-conflicts", mLCOmittedConstraints );
            Statistics::addKeyValuePair( "backjumpings", mBackjumpings );
            Statistics::addKeyValuePair( "omitted-constraints-by-backjumping", mBJOmittedConstraints );
            Statistics::addKeyValuePair( "branching-lemmas", mBranchingLemmas );
        }
        
        void check()
        {
            ++mChecks;
        }
        
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
