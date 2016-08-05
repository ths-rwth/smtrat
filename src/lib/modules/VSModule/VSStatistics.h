/** 
 * @file   VSStatistics.h
 *         Created on April 20, 2016, 11:15 PM
 * @author: Florian Corzilius
 *
 * 
 */

#pragma once

#include "../../utilities/stats/Statistics.h"
#ifdef SMTRAT_DEVOPTION_Statistics

namespace smtrat
{
    class VSStatistics : public Statistics
    {
    private:
        // Members.
        carl::uint mChecks;
        carl::uint mCoveringSets;
        double mCoveringSetSavings;
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
            mCoveringSets( 0 ),
            mCoveringSetSavings( 0.0 ),
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
            Statistics::addKeyValuePair( "average-covering-set-gain", (mCoveringSetSavings/(double)mCoveringSets) );
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