/** 
 * @file   SATstatistics.cpp
 *         Created on October 8, 2012, 11:07 PM
 * @author: Sebastian Junges
 *
 * 
 */

#include "SATStatistics.h"
#ifdef SMTRAT_DEVOPTION_Statistics
#include "../../utilities/stats/Statistics.h"
namespace smtrat {

SATstatistics::SATstatistics( ) : Statistics("Minisat", this), mNrLearnedLemmas(0), mInitialTrue(0)
{
}

void SATstatistics::collect() 
{
    Statistics::addKeyValuePair("Nr literals", nrTotalVariables);
    Statistics::addKeyValuePair("Literals initally true", mInitialTrue);
    Statistics::addKeyValuePair("Ratio assigned vars", (float)(nrTotalVariables-nrUnassignedVariables)/(float)nrTotalVariables);
    Statistics::addKeyValuePair("Nr clauses", nrClauses);
    Statistics::addKeyValuePair("Nr lemmas learned", mNrLearnedLemmas);
    
}
}
#endif

