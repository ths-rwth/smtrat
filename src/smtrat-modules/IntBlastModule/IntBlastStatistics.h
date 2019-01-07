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
#include <smtrat-common/statistics/Statistics.h>

namespace smtrat
{
    class IntBlastStatistics : public Statistics
    {
    public:
        // Override Statistics::collect.
        void collect()
        {
        }

        IntBlastStatistics( const std::string& _statisticName ): 
            Statistics( _statisticName )
        {}

        ~IntBlastStatistics() {}
    };
}

#endif
