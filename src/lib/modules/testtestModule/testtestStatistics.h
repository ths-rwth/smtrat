/**
 * @file testtestStatistics.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-05-08
 * Created on 2015-05-08.
 */


#pragma once

#include "../../config.h"
#ifdef SMTRAT_DEVOPTION_Statistics
#include "../../utilities/stats/Statistics.h"

namespace smtrat
{
    class testtestStatistics : public Statistics
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

        testtestStatistics( const std::string& _statisticName ): 
            Statistics( _statisticName, this ),
            mExampleStatistic( 0 )
        {}

        ~testtestStatistics() {}
    };
}

#endif
