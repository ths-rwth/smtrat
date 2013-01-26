/*
 *  SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
 *
 * This file is part of SMT-RAT.
 *
 * SMT-RAT is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMT-RAT is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *
 */


/** 
 * @file   CollectStatistics.cpp
 *       
 * @author: Sebastian Junges
 *
 * 
 */

#include <fstream>
#include <iostream>

#include "../../config.h"
#ifdef GATHER_STATS
#include "StatisticSettings.h"
#include "CollectStatistics.h"
#include "../../modules/GBModule/GBModuleStatistics.h"
namespace smtrat {
StatisticSettings* CollectStatistics::settings = new StatisticSettings();

CollectStatistics::CollectStatistics( )
{
   
}

void CollectStatistics::registerStats(Statistics* _stats) {
    stats.push_back(_stats);
}

void CollectStatistics::produceOutput() 
{
    for(auto it = stats.begin(); it != stats.end(); ++it) {
        (*it)->collect();
    }
    if(settings->exportXml()) 
    {
        exportXML(settings->xmlPath());
    }
    if(settings->printStats())
    {
        print();
    }
}


void CollectStatistics::print(std::ostream& os) {
    std::cout << "**********************************************" << std::endl;
    std::cout << "*                 Statistics                 *" << std::endl;
    std::cout << "**********************************************" << std::endl;
    for(auto it = stats.begin(); it != stats.end(); ++it) {
        (*it)->print();
    }
    
    std::cout << "**********************************************" << std::endl;
}

void CollectStatistics::exportXML(const std::string& pathToFile) {
    std::stringstream stream;
    stream << "<runtimestats>\n";
    for(auto it = stats.begin(); it != stats.end(); ++it) {
        (*it)->generateXML(stream);
    }
    stream << "</runtimestats>";
    
    std::ofstream file;
    file.open(pathToFile, std::ios::out | std::ios::app );
    file << stream.str() << std::endl;
    file.close();
}


std::vector<Statistics*> CollectStatistics::stats = std::vector<Statistics*>();


}

#endif //GATHER_STATS

