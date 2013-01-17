/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
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
 * @file   RuntimeSettingsManager.cpp
 * @author Sebastian Junges
 *
 * @version 10/01/2013
 */

#include "RuntimeSettings.h"
#include <iostream>

namespace smtrat{
    RuntimeSettings::RuntimeSettings() 
    : mSettingsName("")
    {
        
    }
    RuntimeSettings::RuntimeSettings(const std::string& name)
    : mSettingsName(name)
    {
        
    }

    void RuntimeSettings::parseCmdOption(const std::string& keyValueString) {
        
    }
    
    void RuntimeSettings::printHelp(const std::string& prefix) const {
        
    }
    
    std::map<std::string, std::string> RuntimeSettings::splitIntoKeyValues(const std::string& keyValueString, char delimiter) const {
        std::map<std::string, std::string> pairs;
        size_t tokenOff = 0, seperatorOffset = tokenOff;
        size_t equalityOffset;
        while (seperatorOffset != std::string::npos)
        {
            seperatorOffset = keyValueString.find(delimiter, tokenOff);
            size_t tokenLen = (seperatorOffset == std::string::npos) ? seperatorOffset : seperatorOffset++ - tokenOff;
            std::string token = keyValueString.substr(tokenOff, tokenLen);
            if (!token.empty()) 
            {
                equalityOffset = token.find('=',0);
                if(equalityOffset == std::string::npos) 
                {
                    // No equality found, so we only have a key.
                    pairs.insert(KeyValuePair(token, ""));
                    
                }
                else
                {
                    // split token into key and value
                    size_t keyLength = equalityOffset++;
                    std::string key = token.substr(0, keyLength);
                    std::string value = token.substr(equalityOffset);
                    pairs.insert(KeyValuePair(key,value));
                }
            }
            tokenOff = seperatorOffset;
        }
        
        return pairs;
    }
    
    /**
     * Convenience option
     * @param keyvalues The map with the key-value pairs.
     * @param flag The flag that is set if the key is found
     * @param identifier The key searched for in the map of key-value pairs.
     */
    void RuntimeSettings::setFlagIfOptionSet(const std::map<std::string, std::string>& keyvalues, bool & flag, const std::string& identifier) 
    {
        if(keyvalues.count(identifier) > 0) 
        {
            flag = true; 
        }
    }
    
    /**
     * Convenience option
     * @param keyvalues The map with the key-value pairs.
     * @param value The string that is set to the value from the keyvalue pair, if the key exists.
     * @param key The key searched for.
     * @return true, if the key was found.
     */
    bool RuntimeSettings::setValueIfKeyExists(const std::map<std::string,std::string>& keyvalues, std::string& value, const std::string& key)
    {
        std::map<std::string, std::string>::const_iterator it = keyvalues.find(key);
        if(it != keyvalues.end()) 
        {
            value = it->second;
            return true;
        }
        return false;
    }
    
    
    /**
     * Convenience option
     * @param keyvalues The map with the key-value pairs.
     * @param value The string that is set to the value from the keyvalue pair, if the key exists and the value is nonempty.
     * @param key The key searched for.
     * @return true, if the key was found.
     */
    bool RuntimeSettings::setNonEmptyValueIfKeyExists(const std::map<std::string,std::string>& keyvalues, std::string& value, const std::string& key)
    {
        std::map<std::string, std::string>::const_iterator it = keyvalues.find(key);
        if( it != keyvalues.end() ) 
        {
            if( !it->second.empty() ) 
            {
                value = it->second;
            }
            return true;
        }
        return false;
    }
    
    
}
