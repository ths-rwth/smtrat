/** 
 * @file   SATstatistics.cpp
 *         Created on October 8, 2012, 11:07 PM
 * @author: Sebastian Junges
 *
 * 
 */

#include "SATStatistics.h"
#ifdef GATHER_STATS
#include "../../utilities/stats/Statistics.h"
namespace smtrat {

SATstatistics::SATstatistics( ) : Statistics("Minisat", this)
{
}

void SATstatistics::collect() 
{
    Statistics::addKeyValuePair("Nr Vars", nrTotalVariables);
    Statistics::addKeyValuePair("Ratio assigned vars", (float)(nrTotalVariables-nrUnassignedVariables)/(float)nrTotalVariables);
    Statistics::addKeyValuePair("Nr clauses", nrClauses);
    Statistics::addKeyValuePair("Nr lemmas learned", mNrLearnedLemmas);
}
}
#endif

