/**
 * @file SplitSOSStatistics.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-09-10
 * Created on 2015-09-10.
 */


#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <smtrat-common/statistics/Statistics.h>

namespace smtrat
{
    class SplitSOSStatistics : public Statistics
    {
    private:
    public:
        // Override Statistics::collect.
        void collect()
        {
        }

        SplitSOSStatistics( const std::string& _statisticName ): 
            Statistics( _statisticName )
        {}

        ~SplitSOSStatistics() {}
    };
}

#endif
