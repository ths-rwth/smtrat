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
#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/RuntimeSettings.h>

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
        bool mPrintAllModels;
        bool mPrintSimplifiedInput;
        std::string mSimplifiedInputFileName;
        bool mPrintStatistics;
        bool mPrintStrategy;
        bool mExportDIMACS;
        bool mReadDIMACS;
		bool mReadOPB;
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
        
        bool printAllModels() const
        {
            return mPrintAllModels;
        }
        
        bool printInputSimplified() const
        {
            return mPrintSimplifiedInput;
        }
        
        const std::string& simplifiedInputFileName() const
        {
            return mSimplifiedInputFileName;
        }
        
        bool printStatistics() const
        {
            return mPrintStatistics;
        }
        
        bool printStrategy() const
        {
            return mPrintStrategy;
        }
        
        bool exportDIMACS() const
        {
            return mExportDIMACS;
        }
        bool readDIMACS() const
        {
            return mReadDIMACS;
        }
		bool readOPB() const
        {
            return mReadOPB;
        }
        
    protected:
        void printHelp() const;
        void printLicense() const;
        void printVersion() const;
        void printToC() const;
        void printWelcome() const;
        void printInfo() const;
        
    };  
}
