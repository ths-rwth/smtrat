/** 
 * @file   CollectStatistics.cpp
 *       
 * @author: Sebastian Junges
 *
 * 
 */

#include <fstream>
#include <iostream>

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include "StatisticSettings.h"
#include "CollectStatistics.h"
#include <smtrat-modules/GBModule/GBModuleStatistics.h>
namespace smtrat {
StatisticSettings* CollectStatistics::settings = new StatisticSettings();

CollectStatistics::CollectStatistics( )
{}

CollectStatistics::~CollectStatistics( )
{
    while( !stats.empty() )
    {
        Statistics* statToDel = stats.back();
        stats.pop_back();
        delete statToDel;
    }
}

void CollectStatistics::registerStats(Statistics* _stats) {
    stats.push_back(_stats);
}

void CollectStatistics::collect() {
    for(auto it = stats.begin(); it != stats.end(); ++it) {
        (*it)->collect();
        if( (*it)->maxKeyLength() > maxKeyLength )
            maxKeyLength = (*it)->maxKeyLength();
        if( (*it)->name().size() > maxNameLength )
            maxNameLength = (*it)->name().size();
    }
}

void CollectStatistics::print(bool smtlib) {
    if(settings->printStats())
    {
        if(smtlib)
        {
            for(auto it = stats.begin(); it != stats.end(); ++it)
                (*it)->print(settings->rOutputChannel(), true, maxNameLength, maxKeyLength );
        }
        else
        {
            settings->rOutputChannel() << "**********************************************" << std::endl;
            settings->rOutputChannel() << "*                 Statistics                 *" << std::endl;
            settings->rOutputChannel() << "**********************************************" << std::endl;
            for(auto it = stats.begin(); it != stats.end(); ++it) {
                (*it)->print();

            settings->rOutputChannel() << "* * * * * * * * * * * * * * * * * * * * * * * " << std::endl;
            }

            settings->rOutputChannel() << "**********************************************" << std::endl;
        }
    }
}

void CollectStatistics::exportXML() {
    std::stringstream stream;
    stream << "<runtimestats>\n";
    for(auto it = stats.begin(); it != stats.end(); ++it) {
        (*it)->generateXML(stream);
    }
    stream << "</runtimestats>";
    
    std::ofstream file;
    file.open(settings->xmlPath(), std::ios::out | std::ios::app );
    file << stream.str() << std::endl;
    file.close();
}

std::vector<Statistics*> CollectStatistics::stats = std::vector<Statistics*>();
size_t CollectStatistics::maxNameLength = 0;
size_t CollectStatistics::maxKeyLength = 0;


}

#endif //SMTRAT_DEVOPTION_Statistics

