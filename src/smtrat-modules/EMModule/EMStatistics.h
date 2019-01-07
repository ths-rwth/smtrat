/**
 * @file EMStatistics.h
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
    class EMStatistics : public Statistics
    {
    private:
        // Members.
        /**
         * Example for a statistic.
         */
        std::size_t mExampleStatistic = 0;

    public:
        // Override Statistics::collect.
        void collect()
        {
           Statistics::addKeyValuePair( "example_statistic", mExampleStatistic );
        }

        void foo()
        {
            ++mExampleStatistic;
        }

        EMStatistics( const std::string& _statisticName ): 
            Statistics( _statisticName )
        {}

        ~EMStatistics() {}
    };
}

#endif
