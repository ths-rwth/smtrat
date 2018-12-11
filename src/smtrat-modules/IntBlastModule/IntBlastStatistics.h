/**
 * @file IntBlastStatistics.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-05-12
 * Created on 2015-05-12.
 */


#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <lib/utilities/stats/Statistics.h>

namespace smtrat
{
    class IntBlastStatistics : public Statistics
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

        IntBlastStatistics( const std::string& _statisticName ): 
            Statistics( _statisticName, this ),
            mExampleStatistic( 0 )
        {}

        ~IntBlastStatistics() {}
    };
}

#endif
