/**
 * @file ESStatistics.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-09-09
 * Created on 2015-09-09.
 */


#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <lib/utilities/stats/Statistics.h>

namespace smtrat
{
    class ESStatistics : public Statistics
    {
    private:
        // Members.
        /**
         * Example for a statistic.
         */
        size_t mExampleStatistic;

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

        ESStatistics( const std::string& _statisticName ): 
            Statistics( _statisticName, this ),
            mExampleStatistic( 0 )
        {}

        ~ESStatistics() {}
    };
}

#endif
