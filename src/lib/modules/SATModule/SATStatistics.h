/** 
 * @file   SATstatistics.h
 *         Created on October 8, 2012, 11:07 PM
 * @author: Sebastian Junges
 *
 * 
 */

#ifndef SATSTATISTICS_H
#define	SATSTATISTICS_H

#include "../../utilities/stats/Statistics.h"
#ifdef GATHER_STATS

namespace smtrat {

class SATstatistics : public Statistics
{
public:
    SATstatistics( );
    virtual ~SATstatistics( ) {}
    /**
     * override
     */
    void collect();
    void lemmaLearned() {
        mNrLearnedLemmas++;
    }
    void initialTrue() {
        mInitialTrue++;
    }
public:
    unsigned nrTotalVariables;
    unsigned nrUnassignedVariables;
    unsigned nrClauses;
protected:
    unsigned mNrLearnedLemmas;
    unsigned mInitialTrue;
private:

};

}
#endif

#endif	/* SATSTATISTICS_H */

