/**
 * @file FouMoStatistics.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2014-12-01
 * Created on 2014-12-01.
 */


#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <smtrat-common/statistics/Statistics.h>

namespace smtrat
{
    class FouMoStatistics : public Statistics
    {
    public:
        // Override Statistics::collect.
        void collect()
        {
        }

        FouMoStatistics( const std::string& _statisticName ): 
            Statistics( _statisticName )
        {}

        ~FouMoStatistics() {}
    };
}

#endif
