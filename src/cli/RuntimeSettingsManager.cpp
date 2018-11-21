/** 
 * @file   RuntimeSettingsManager.cpp
 * @author Sebastian Junges
 * @author Florian Corzilius
 * @since   2013-01-10
 * @version 2013-10-30
 */

#include <stdio.h>
#include <string.h>
#include <map>
#include <iostream>
#include <fstream>
#include <istream>
#include <algorithm>

#include "RuntimeSettingsManager.h"
#include "ExitCodes.h"

#include "../lib/modules/Modules.h"
#include "config.h"

#include <carl/util/CompileInfo.h>
#include <smtrat-common/smtrat-common.h>

#include "../lib/utilities/SettingsManager.h"

namespace smtrat
{

RuntimeSettingsManager::RuntimeSettingsManager() : 
    mSettingObjects(),
    mDoPrintTimings( false ), 
    mPrintModel( false ),
    mPrintAllModels( false ),
    mPrintSimplifiedInput( false ),
    mSimplifiedInputFileName( "" ),
    mPrintStatistics( false ),
    mPrintStrategy( false ),
    mExportDIMACS( false ),
    mReadDIMACS( false ),
	mReadOPB( false )
{}

/**
 * Add a settings object with a unique name
 * @param name A unique string not yet in the list of settingsobjects. The name will be used as identifier and for passing command line arguments.
 * @param settings A pointer to the object.
 */
void RuntimeSettingsManager::addSettingsObject(const std::string& name, RuntimeSettings* settings) 
{
    assert(mSettingObjects.count(name) == 0);
    assert(settings != NULL);
    
    mSettingObjects[name] = settings;
}

/**
 * A list of names and settings objects as a convenient function to introduce multiple settingsobjects to the manager.
 * @param settings
 */
void RuntimeSettingsManager::addSettingsObject(const std::list<std::pair<std::string,RuntimeSettings*> >& settings) 
{
    for(std::list<std::pair<std::string, RuntimeSettings*> >::const_iterator it = settings.begin(); it != settings.end(); ++it)
    {
        addSettingsObject(it->first, it->second);
    }
}
/**
 * Return a object with settings
 * @param name The name of the requested object.
 * @return A pointer to the settings object identified by name.
 */
RuntimeSettings* RuntimeSettingsManager::getSettingsObject(const std::string& name) const 
{
    return mSettingObjects.at(name);
}

/**
 * Parse the command line arguments
 * @param argc Number of arguments
 * @param argv Argument values
 * @return the path for the inputfile.
 */
std::string RuntimeSettingsManager::parseCommandline(int argc, char** argv) 
{
    // If no arguments are given, print a welcome message.
    if(argc==1)
    {
        printWelcome();
    }
    // Iterate over the given arguments.
    for(int argi = 1; argi < argc; ++argi) 
    {
        // Check if a option is passed.
        bool foundOption = strlen(argv[argi]) > 2 && argv[argi][0] == '-' && argv[argi][1] == '-';
        bool foundOptionShortcut = strlen(argv[argi]) > 1 && argv[argi][0] == '-' && argv[argi][1] != '-';
        if( foundOption || foundOptionShortcut )
        {
            std::string optionName( argv[argi] + ( foundOptionShortcut ? 1 : 2 ) );
            // check for global options.
            if(optionName == "help" || optionName == "h") 
            {
                printHelp();
                exit(SMTRAT_EXIT_SUCCESS);
            }
            else if(optionName == "settings")
            {
                std::cout << SettingsManager::getInstance().changed() << std::endl;
                exit(SMTRAT_EXIT_SUCCESS);
            }
            else if(optionName == "all-settings")
            {
                std::cout << SettingsManager::getInstance().all() << std::endl;
                exit(SMTRAT_EXIT_SUCCESS);
            }
            else if(optionName == "cmake")
            {
                std::cout << "CMake options used for CArL:" << std::endl;
                std::cout << carl::CMakeOptions() << std::endl;
                std::cout << std::endl;
                std::cout << "CMake options used for SMT-RAT:" << std::endl;
                std::cout << smtrat::CMakeOptions() << std::endl;
                exit(SMTRAT_EXIT_SUCCESS);
            }
            else if(optionName == "export-dimacs")
            {
                mExportDIMACS = true;
            }
            else if(optionName == "dimacs")
            {
                mReadDIMACS = true;
            }
			else if(optionName == "opb")
            {
                mReadOPB = true;
            }
            else if(optionName == "license") 
            {
                printLicense();
                exit(SMTRAT_EXIT_SUCCESS);
            }
//            else if(optionName == "toc") 
//            {
//                printToC();
//                exit(SMTRAT_EXIT_SUCCESS);
//            }
            else if(optionName == "list-modules")
            {
                printModulesInfo();
                exit(SMTRAT_EXIT_SUCCESS);
            }
            #ifdef SMTRAT_DEVOPTION_MeasureTime
            else if(optionName == "print-timings")
            {
                mDoPrintTimings = true;
            }
            #endif
            else if(optionName == "info")
            {
                printInfo();
                exit(SMTRAT_EXIT_SUCCESS);
            }
            else if(optionName == "version" || optionName == "v")
            {
                printVersion();
                exit(SMTRAT_EXIT_SUCCESS);
            }
            else if(optionName == "model" || optionName == "m")
            {
                mPrintModel = true;
            }
            else if(optionName == "all-model" || optionName == "a")
            {
                mPrintAllModels = true;
            }
            else if(optionName == "simplified-input" || optionName == "si")
            {
                mPrintSimplifiedInput = true;
            }
            else if(optionName.substr( 0, 17 ) == "simplified-input:" || optionName.substr( 0, 3 ) == "si:")
            {
                auto pos = optionName.find(":");
                if( pos != std::string::npos )
                {
                    mSimplifiedInputFileName = optionName.substr( pos+1, optionName.size() - pos );
                }
                mPrintSimplifiedInput = true;
            }
            else if(optionName == "statistics" || optionName == "s")
            {
                mPrintStatistics = true;
            }
            else if(optionName == "print-strategy")
            {
                mPrintStrategy = true;
                return "";
            }
            // no more global options, so we expect module options
            else
            {
                if( foundOptionShortcut )
                {
                    std::cerr << "Unknown option short cut: " << argv[argi] << std::endl;
                    exit(SMTRAT_EXIT_UNEXPECTED_INPUT);
                }
                size_t semicolonPosition(optionName.find(':'));
                // Check if a semicolon was found
                if(semicolonPosition == optionName.npos) 
                {
                    std::cerr << "Unknown option: " << argv[argi] << std::endl;
                    exit(SMTRAT_EXIT_UNEXPECTED_INPUT);
                }
                // Split into  name and keyvalue string.
                std::string settingsObjectName = optionName.substr(0,semicolonPosition);
                std::string keyValueString = optionName.substr(semicolonPosition+1);

                // Check safely and without exception-usage whether such a module exists.
                if(mSettingObjects.count(settingsObjectName) == 0) 
                {
                    std::cerr << "No such module: " << settingsObjectName << std::endl;
                    exit(SMTRAT_EXIT_UNEXPECTED_INPUT);
                }
                mSettingObjects.at(settingsObjectName)->parseCmdOption(keyValueString);
            }
        } 
        else 
        {
            // this should be an input file, so we return it.
            // If there are options after the input, we write a warning to the errorstream.
            if(argi + 1 < argc)
            {
                std::cerr << "Warning, unparsed options after file. These are ignored." << std::endl;
            }
            return std::string(argv[argi]);
        }
    }
    // No input file recognized, and no other mode (--help or likewise) entered, so we exit with a failure.
    std::cerr << "No input file recognized" << std::endl;
    exit(SMTRAT_EXIT_UNEXPECTED_INPUT);
}
        
/**
 * Print help statement.
 */
void RuntimeSettingsManager::printHelp() const
{
    // Print usage examples.
    std::cout << "Usage: ./smtrat [GlobalOptions] [ModuleOptions] inputfile" << std::endl;
    std::cout << "Example: ./smtrat --help. Prints this help." << std::endl;
    std::cout << "Example ./smtrat --parser:s example.smt2. Runs SMT-RAT on example.smt2 with tracing enabled for the parser." << std::endl;
    std::cout << std::endl;
    // Print help for the global options.
    std::cout << "Global options:" << std::endl;
    std::cout << "\t --cmake \t\t\t print cmake options" << std::endl;
    std::cout << "\t --help (-h) \t\t\t prints this help" << std::endl;
    std::cout << "\t --info \t\t\t prints information about the binary" << std::endl;
    std::cout << "\t --license \t\t\t prints the license" << std::endl;
    std::cout << "\t --version (-v) \t\t prints the current version" << std::endl;
    std::cout << std::endl;
    std::cout << "Solver information:" << std::endl;
    std::cout << "\t --statistics (-s) \t\t prints any statistics collected in the solving process" << std::endl;
    std::cout << "\t --print-strategy \t\t prints the strategy of this solver" << std::endl;
    std::cout << std::endl;
    std::cout << "Solving options:" << std::endl;
    std::cout << "\t --model (-m) \t\t\t prints a model is printed if the example is found to be satisfiable" << std::endl;
    std::cout << "\t --all-models (-a) \t\t prints all models if the example is found to be satisfiable" << std::endl;
    std::cout << "\t --simplified-input (-si) \t prints a simplified form of the input formula (if result is unknown)" << std::endl;
    std::cout << std::endl;
    std::cout << "Developer options:" <<std::endl;
    std::cout << "\t --list-modules \t\t prints all compiled modules" << std::endl;
    #ifdef SMTRAT_DEVOPTION_MeasureTime
    std::cout << "\t --print-timings \t prints the timings" << std::endl;
    #endif
    std::cout << std::endl;
    // Print help for all known modules.
    if( !mSettingObjects.empty() )
    {
        std::cout << "Module options:" << std::endl;
        for( std::map<std::string, RuntimeSettings*>::const_iterator it = mSettingObjects.begin(); it != mSettingObjects.end(); ++it )
        {
            std::cout << "- Module: " << it->first << std::endl;
            it->second->printHelp("\t");
            std::cout << std::endl;
        }
        std::cout << std::endl;
    }
    // Print reference to website.
    std::cout << "For more information, please visit our website at " << SMTRAT_WEBSITE << std::endl;
}

/**
 * Print license.
 */
void RuntimeSettingsManager::printLicense() const 
{
    std::string license = LICENSE_CONTENT;
    std::replace( license.begin(), license.end(), ';', '\n');
    std::cout << license << std::endl;
}

/**
 * Print version.
 */
void RuntimeSettingsManager::printVersion() const 
{
    std::cout << SMTRAT_VERSION << std::endl;
}

/**
 * Print Terms of Conduct
 */
void RuntimeSettingsManager::printToC() const
{
    
}

/**
 * Print message when no arguments are given.
 */
void RuntimeSettingsManager::printWelcome() const 
{
    std::cout << "This is " << SMTRAT_PROJECT_NAME << "." << std::endl;
    std::cout << "Version: " << SMTRAT_VERSION << std::endl;
    std::cout << "For more information, run this binary with --help." << std::endl;
    std::cout << std::endl << std::endl;
    printLicense();
}

void RuntimeSettingsManager::printInfo() const
{
    std::cout << "Code was compiled with compiler " << smtrat::CompileInfo::CXXCompiler << " " << smtrat::CompileInfo::CXXCompilerVersion << std::endl;
    std::cout << "Build type:" << smtrat::CompileInfo::BuildType << std::endl;   
    std::cout << "Code is based on commit " << smtrat::CompileInfo::GitRevisionSHA1 << ". " << std::endl;
    std::cout << "Build on a " << smtrat::CompileInfo::SystemName << " (" << CompileInfo::SystemVersion << ") machine." << std::endl;
    std::cout << "Version: " << SMTRAT_VERSION << std::endl;
}

}
