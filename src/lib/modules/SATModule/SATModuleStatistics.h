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
        unsigned mNrTotalVariables;
        unsigned mNrClauses;
        unsigned mNrLearnedLemmas;
        unsigned mVarsWithPolarityTrue;
        unsigned mPropagations;
        unsigned mRestarts;
        unsigned mDecisions;

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

        virtual ~SATModuleStatistics() {}

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
        
        unsigned& rNrClauses()
        {
            return mNrClauses;
        }
        
        unsigned& rNrTotalVariables()
        {
            return mNrTotalVariables;
        }

    };

}
#endif

#endif	/* SATMODULESTATISTICS_H */

