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
    

