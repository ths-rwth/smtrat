/** 
 * @file   RuntimeSettingsManager.h
 * @author Sebastian Junges
 * @author Florian Corzilius
 * @since   2013-01-10
 * @version 2013-10-30
 */

#pragma once

#include <string>
#include <assert.h>
#include <list>
#include "../lib/solver/RuntimeSettings.h"

namespace smtrat
{    
    /**
     * Structure which holds all the different runtime-settings.
     */
    class RuntimeSettingsManager  {
    protected:
        std::map<std::string, RuntimeSettings*> mSettingObjects;
        bool mDoPrintTimings;
        bool mPrintModel;
        bool mPrintStatistics;
    public:
        RuntimeSettingsManager();
        virtual ~RuntimeSettingsManager() {}
        
        void addSettingsObject(const std::string& name, RuntimeSettings* settings);
        void addSettingsObject(const std::list<std::pair<std::string, RuntimeSettings*> >& settings);
        RuntimeSettings* getSettingsObject(const std::string& name) const;
        std::string parseCommandline(int argc, char** argv);
        
        bool doPrintTimings() const
        {
            return mDoPrintTimings;
        }
        
        bool printModel() const
        {
            return mPrintModel;
        }
        
        bool printStatistics() const
        {
            return mPrintStatistics;
        }
        
    protected:
        void printHelp() const;
        void printWarranty() const;
        void printToC() const;
        void printWelcome() const;
        void printInfo() const;
        
    };  
}



