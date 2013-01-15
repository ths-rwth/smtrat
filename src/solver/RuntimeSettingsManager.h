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
 * @file   RuntimeSettingsManager.h
 * @author Sebastian Junges
 *
 * @version 10/01/2013
 */

#pragma once

#include <string>
#include <assert.h>
#include <list>
#include "../lib/RuntimeSettings.h"

namespace smtrat {
   
    struct ParserSettings : RuntimeSettings {
        
    };

    /**
     * Structure which holds the runtime-settings for validation.
     */
    struct ValidationSettings : RuntimeSettings {
        bool enabled;
        std::string pathToAssumptions;
    };

    /**
     * Structure which holds the runtime-settings for statistics.
     */
    struct StatisticSettings : RuntimeSettings {
        bool enabled;
        std::string xmlOutputfile;
    };
    
    /**
     * Structure which holds all the different runtime-settings.
     */
    class RuntimeSettingsManager  {
    protected:
        std::map<std::string, RuntimeSettings*> mSettingObjects;
    public:
        void addSettingsObject(const std::string& name, RuntimeSettings* settings);
        void addSettingsObject(const std::list<std::pair<std::string, RuntimeSettings*> >& settings);
        RuntimeSettings* getSettingsObject(const std::string& name) const;
        std::string parseCommandline(int argc, char** argv);
        
    protected:
        void printHelp() const;
        void printWarranty() const;
        void printToC() const;
        void printWelcome() const;
    };  
}



