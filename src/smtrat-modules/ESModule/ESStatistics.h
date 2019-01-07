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
#include <smtrat-common/statistics/Statistics.h>

namespace smtrat
{
    class ESStatistics : public Statistics
    {
    private:

    public:
        // Override Statistics::collect.
        void collect()
        {
        }

        ESStatistics( const std::string& _statisticName ): 
            Statistics( _statisticName )
        {}

        ~ESStatistics() {}
    };
}

#endif
