/**
 * @file IncWidthStatistics.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-06-29
 * Created on 2015-06-29.
 */


#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <smtrat-common/statistics/Statistics.h>

namespace smtrat
{
    class IncWidthStatistics : public Statistics
    {
    public:
        // Override Statistics::collect.
        void collect()
        {
        }

        IncWidthStatistics( const std::string& _statisticName ): 
            Statistics( _statisticName )
        {}

        ~IncWidthStatistics() {}
    };
}

#endif
