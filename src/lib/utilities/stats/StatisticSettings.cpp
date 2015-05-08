/** 
 * @file   StatisticSettings.cpp
 * @author: Sebastian Junges
 *
 */
#include "StatisticSettings.h"

namespace smtrat {
StatisticSettings::StatisticSettings() : 
    mExportXml(false),
    mXmlPath("stats.xml"),
    mPrintStats(false),
    mOutputChannel(std::cout.rdbuf())
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

