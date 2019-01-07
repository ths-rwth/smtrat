/** 
 * @file   StatisticSettings.h
 * @author: Sebastian Junges
 *
 */
#pragma once

#include <iostream>
#include <smtrat-common/settings/RuntimeSettings.h>

namespace smtrat {
class StatisticSettings : public RuntimeSettings
{
protected:    
    bool        mExportXml;
    std::string mXmlPath;
    bool        mPrintStats;
    std::ostream mOutputChannel;
public:
    StatisticSettings();
    
    void parseCmdOption(const std::string& keyValueString);
    void printHelp(const std::string& prefix) const;
    
    bool exportXml() const;
    bool printStats() const;
    const std::string& xmlPath() const;
    
    void setPrintStats( bool _printStats )
    {
        mPrintStats = _printStats;
    }
    
    std::ostream& rOutputChannel()
    {
        return mOutputChannel;
    }

};
}
