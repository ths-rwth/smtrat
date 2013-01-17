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
 * @file   StatisticSettings.cpp
 * @author: Sebastian Junges
 *
 */
#include "StatisticSettings.h"
#include <iostream>

namespace smtrat {
StatisticSettings::StatisticSettings() : 
    mExportXml(false),
    mXmlPath("stats.xml"),
    mPrintStats(false)
{
    
}

void StatisticSettings::printHelp(const std::string& prefix) const
{
    std::cout << prefix <<  "Seperate options by a comma." << std::endl;
    std::cout << prefix <<  "Options:" << std::endl;
    std::cout << prefix <<  "\t exportXml[=<path>] \t Export the stats to a file located at path." << std::endl;
    std::cout << prefix <<  "\t\t\t\t If path is not set, stats.xml is used." << std::endl;
    std::cout << prefix <<  "\t print \t\t\t Print to std::cout after finishing." << std::endl;
}

    void StatisticSettings::parseCmdOption(const std::string& keyValueString) 
    {
        std::map<std::string, std::string> keyvalues = splitIntoKeyValues(keyValueString);
        setFlagIfOptionSet(keyvalues, mPrintStats, "print");
        mExportXml = setNonEmptyValueIfKeyExists(keyvalues, mXmlPath, "exportXml");
    }
    
    bool StatisticSettings::exportXml() const 
    {
        return mExportXml;
    }
    
    bool StatisticSettings::printStats() const 
    {
        return mPrintStats;
    }
    
    const std::string& StatisticSettings::xmlPath() const 
    {
        return mXmlPath;
    }

}

