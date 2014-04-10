/** 
 * @file   SATstatistics.h
 *         Created on October 8, 2012, 11:07 PM
 * @author: Sebastian Junges
 *
 * 
 */

#ifndef SATMODULESTATISTICS_H
#define	SATMODULESTATISTICS_H

#include "../../utilities/stats/Statistics.h"
#ifdef SMTRAT_DEVOPTION_Statistics

namespace smtrat
{
    class SATModuleStatistics : public Statistics
    {
    private:
        // Members.
        size_t mNrTotalVariables;
        size_t mNrClauses;
        size_t mNrLearnedLemmas;
        size_t mVarsWithPolarityTrue;
        size_t mPropagations;
        size_t mRestarts;
        size_t mDecisions;

    public:
        SATModuleStatistics( const std::string& _name ) : 
            Statistics( _name, this ),
            mNrTotalVariables( 0 ),
            mNrClauses( 0 ),
            mNrLearnedLemmas( 0 ), 
            mVarsWithPolarityTrue( 0 ), 
            mPropagations( 0 ), 
            mRestarts( 0 ), 
            mDecisions( 0 )
        {}

        ~SATModuleStatistics() {}

        void collect()
        {
            Statistics::addKeyValuePair( "literals", mNrTotalVariables );
            Statistics::addKeyValuePair( "literals_initally_true", mVarsWithPolarityTrue );
            Statistics::addKeyValuePair( "clauses", mNrClauses );
            Statistics::addKeyValuePair( "lemmas_learned", mNrLearnedLemmas );
            Statistics::addKeyValuePair( "propagations", mPropagations );
            Statistics::addKeyValuePair( "decisions", mDecisions );
            Statistics::addKeyValuePair( "restarts", mRestarts );
        }

        void lemmaLearned()
        {
            ++mNrLearnedLemmas;
        }

        void initialTrue()
        {
            ++mVarsWithPolarityTrue;
        }

        void propagate()
        {
            ++mPropagations;
        }

        void decide()
        {
            ++mDecisions;
        }

        void restart()
        {
            ++mRestarts;
        }
        
        size_t& rNrClauses()
        {
            return mNrClauses;
        }
        
        size_t& rNrTotalVariables()
        {
            return mNrTotalVariables;
        }

    };

}
#endif

#endif	/* SATMODULESTATISTICS_H */

