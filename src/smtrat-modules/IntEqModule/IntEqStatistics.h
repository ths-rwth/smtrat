/**
 * @file IntEqStatistics.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2014-11-24
 * Created on 2014-11-24.
 */


#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <smtrat-common/statistics/Statistics.h>

namespace smtrat
{
    class IntEqStatistics : public Statistics
    {
    public:
        // Override Statistics::collect.
        void collect()
        {
        }

        IntEqStatistics( const std::string& _statisticName ): 
            Statistics( _statisticName )
        {}

        ~IntEqStatistics() {}
    };
}

#endif
