/** 
 * @file   CNFerModuleStatistics.h
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
    class CNFerModuleStatistics : public Statistics
    {
    private:
        // Members.
        size_t mBooleanComplexity = 1;
        size_t mNrOfArithVariables = 0;
        size_t mNrOfBoolVariables = 0;

    public:

        void collect()
        {
            Statistics::addKeyValuePair( "boolean_complexity", mBooleanComplexity );
            Statistics::addKeyValuePair( "nr_of_arith_variables", mNrOfArithVariables );
            Statistics::addKeyValuePair( "nr_of_bool_variables", mNrOfBoolVariables );
        }

        void addClauseOfSize(size_t _clauseSize)
        {
            unsigned targetlevel = 0;
            while (_clauseSize >>= 1) ++targetlevel;
            mBooleanComplexity += targetlevel;
        }
        
        size_t& nrOfArithVariables()
        {
            return mNrOfArithVariables;
        }
        
        size_t& nrOfBoolVariables()
        {
            return mNrOfBoolVariables;
        }

    };

}
#endif
