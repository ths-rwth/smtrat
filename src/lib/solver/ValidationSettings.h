/**
 * @file ValidationSettings.h
 * @author Sebastian Junges
 * @version 2013-01-16
 */

#pragma once

#include "RuntimeSettings.h"
#include <string>

namespace smtrat 
{
class ValidationSettings : public RuntimeSettings
{
protected:
    /// Logging of lemmata
    bool mLogLemmata;
    /// Logging of theory calls
    bool mLogTCalls;
    /// Logging of infeasible subsets
    bool mLogInfSubsets;
    /// Path were assumptions file should be saved.
    std::string mPath;
public:
    ValidationSettings();
    
    void parseCmdOption(const std::string& keyValueString);
    void printHelp(const std::string& prefix) const;
    
    bool logLemmata() const;
    bool logTCalls() const;
    bool logInfSubsets() const;
    const std::string& path() const;
    
    
};

}
