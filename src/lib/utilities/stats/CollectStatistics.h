/** 
 * @file   CollectStatistics.h
 * @author: Sebastian Junges
 *
 */

#pragma once

#include <smtrat-common/smtrat-common.h>
#include "StatisticSettings.h"


#ifdef SMTRAT_DEVOPTION_Statistics

#include <vector>
#include <iostream>
/*
namespace smtrat {

    class Statistics;
    
    class CollectStatistics
    {
    public:
        CollectStatistics( );
        ~CollectStatistics();
        
        static StatisticSettings* settings;
        static void registerStats(Statistics* _stats);
        static void collect();
        static void exportXML();
        static void print(bool smtlib = false);
    protected:
        static void exportKeyValue(std::string path);
    private:
        static std::vector<Statistics*> stats;
        static size_t maxNameLength;
        static size_t maxKeyLength;
    };
}
*/
#endif
