/**
 * @file ValidationSettings.cpp
 * @author Sebastian Junges
 * @version 2013-01-16
 */

#include "ValidationSettings.h"
#include <string>
#include <iostream>

namespace smtrat
{
    ValidationSettings::ValidationSettings() :
        mLogLemmata(false),
        mLogTCalls(false),
        mLogInfSubsets(false),
        mPath("assumptions.smt2")    
    {
        
    }


    void ValidationSettings::parseCmdOption(const std::string& keyValueString) 
    {
        std::map<std::string, std::string> keyvalues = splitIntoKeyValues(keyValueString);
        if(keyvalues.count("log-all") > 0) 
        {
            mLogLemmata = true;
            mLogTCalls = true;
            mLogInfSubsets = true;
        }
        else
        {
            // Yes, this is in nlogn but it is more readable then if it is in n. And n is small anyway.
            setFlagIfOptionSet(keyvalues, mLogLemmata, "log-lemmata");
            setFlagIfOptionSet(keyvalues, mLogTCalls, "log-tcalls");
            setFlagIfOptionSet(keyvalues, mLogInfSubsets, "log-infsubsets");
        }
        setValueIfKeyExists(keyvalues, mPath, "path");
    }

    void ValidationSettings::printHelp(const std::string& prefix) const
    {
        std::cout << prefix <<  "Seperate options by a comma." << std::endl;
        std::cout << prefix <<  "Options:" << std::endl;
        std::cout << prefix <<  "\t log-all \t\t Log all intermediate steps." << std::endl;
        std::cout << prefix <<  "\t log-lemmata \t\t Enables logging of produced lemmata." << std::endl;
        std::cout << prefix <<  "\t log-tcalls \t\t Enables logging of theory calls" << std::endl;
        std::cout << prefix <<  "\t log-infsubsets \t Enalbes logging of the infeasible subsets" << std::endl;
        std::cout << prefix <<  "\t path=<value> \t\t Sets the output path. Default is assumptions.smt2" << std::endl;
    }

    bool ValidationSettings::logTCalls() const 
    {
        return mLogTCalls;
    }
    
    bool ValidationSettings::logLemmata() const 
    {
        return mLogLemmata;
    }
    
    bool ValidationSettings::logInfSubsets() const
    {
        return mLogInfSubsets;
    }
    
    const std::string& ValidationSettings::path() const
    {
        return mPath;
    }
            
}


