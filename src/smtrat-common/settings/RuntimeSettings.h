/** 
 * @file   RuntimeSettings.h
 * @author Sebastian Junges
 *
 * @version 10/01/2013
 */

#pragma once
#include <string>
#include <map>

namespace smtrat{
/**
 * A base class for settings which can be passed to the modules.
 */
class RuntimeSettings 
{
    protected:
        std::string mSettingsName;
    public:
        RuntimeSettings();
        RuntimeSettings(const std::string& name);
        virtual ~RuntimeSettings();
        virtual void parseCmdOption(const std::string& keyValueString);
        virtual void printHelp(const std::string& prefix) const;
    protected:
        typedef std::pair<std::string, std::string> KeyValuePair;
        // convenience methods
        std::map<std::string, std::string> splitIntoKeyValues(const std::string& keyValueString, char delimiter = ',') const;
        void setFlagIfOptionSet(const std::map<std::string, std::string>& keyvalues, bool & flag, const std::string& identifier);
        bool setValueIfKeyExists(const std::map<std::string, std::string>& keyvalues, std::string & value, const std::string& key );
        bool setNonEmptyValueIfKeyExists(const std::map<std::string, std::string>& keyvalues, std::string & value, const std::string& key );
};
}
    

