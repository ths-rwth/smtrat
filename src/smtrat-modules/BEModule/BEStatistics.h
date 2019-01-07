/**
 * @file BEStatistics.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-09-09
 * Created on 2015-09-09.
 */


#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <smtrat-common/statistics/Statistics.h>

namespace smtrat
{
    class BEStatistics : public Statistics
    {
    public:
        // Override Statistics::collect.
        void collect()
        {
        }

        BEStatistics( const std::string& _statisticName ): 
            Statistics( _statisticName )
        {}

        ~BEStatistics() {}
    };
}

#endif
