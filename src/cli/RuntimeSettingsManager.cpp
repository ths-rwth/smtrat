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
 * @author Florian Corzilius
 * @since   2013-01-10
 * @version 2013-10-30
 */

#include <stdio.h>
#include <string.h>
#include <map>
#include <iostream>

#include "RuntimeSettingsManager.h"
#include "ExitCodes.h"

#include "../lib/modules/Modules.h"
#include "../lib/config.h"
#include "../lib/solver/CompileInfo.h"

#include "carl/util/CMakeOptions.h"
#include "../lib/utilities/CMakeOptions.h"

#include "../lib/utilities/SettingsManager.h"

namespace smtrat
{

RuntimeSettingsManager::RuntimeSettingsManager() : 
    mDoPrintTimings( false ), 
    mPrintModel( false ),
    mPrintStatistics( false )
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
        bool foundOptionShortcut = strlen(argv[argi]) == 2 && argv[argi][0] == '-';
        if( foundOption || foundOptionShortcut )
        {
            std::string optionName( argv[argi] + ( foundOptionShortcut ? 1 : 2 ) );
            // check for global options.
            if(optionName == "help") 
            {
                printHelp();
                exit(SMTRAT_EXIT_SUCCESS);
            }
			else if(optionName == "settings") {
				std::cout << SettingsManager::getInstance().changed() << std::endl;
                exit(SMTRAT_EXIT_SUCCESS);
			}
			else if(optionName == "all-settings") {
				std::cout << SettingsManager::getInstance().all() << std::endl;
                exit(SMTRAT_EXIT_SUCCESS);
			}
			else if(optionName == "cmake")
			{
				std::cout << "CMake options used for CArL:" << std::endl;
				carl::printCMakeOptions(std::cout);
				std::cout << std::endl;
				std::cout << "CMake options used for SMT-RAT:" << std::endl;
				smtrat::printCMakeOptions(std::cout);
				std::cout << std::endl;
			}
            else if(optionName == "warranty") 
            {
                printWarranty();
                exit(SMTRAT_EXIT_SUCCESS);
            }
            else if(optionName == "toc") 
            {
                printToC();
                exit(SMTRAT_EXIT_SUCCESS);
            }
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
            else if(optionName == "info")
            {
                printInfo();
                exit(SMTRAT_EXIT_SUCCESS);
            }
            #endif
            else if(optionName == "model" || optionName == "m")
            {
                mPrintModel = true;
            }
            else if(optionName == "statistics" || optionName == "s")
            {
                mPrintStatistics = true;
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
    std::cout << "Usage: ./solver [GlobalOptions] [ModuleOptions] inputfile" << std::endl;
    std::cout << "Example: ./solver --help. Prints this help." << std::endl;
    std::cout << "Example ./solver --parser:s example.smt2. Runs the solver on example.smt2 with tracing enabled for the parser." << std::endl;
    std::cout << std::endl;
    // Print help for the global options.
    std::cout << "Global options:" << std::endl;
    std::cout << "\t --help \t\t prints this help." << std::endl;
	std::cout << "\t --cmake \t\t print cmake options." << std::endl;
    std::cout << "\t --warranty \t\t prints the warranty." << std::endl;
    std::cout << "\t --toc  \t\t\t prints the terms of condition" << std::endl;
    std::cout << "\t --info \t\t\t prints information about the binary" << std::endl;
    std::cout << "\t --model (-m) \t\t\t prints a model is printed if the example is found to be satisfiable" << std::endl;
    std::cout << "\t --statistics (-s) \t\t\t prints any statistics collected in the solving process" << std::endl;
    std::cout << std::endl;
    std::cout << "Developer options:" <<std::endl;
    std::cout << "\t --list-modules \t prints all compiled modules" << std::endl;
    #ifdef SMTRAT_DEVOPTION_MeasureTime
    std::cout << "\t --print-timings \t prints the timings" << std::endl;
    #endif
    std::cout << std::endl;
    // Print help for all known modules.
    std::cout << "Module options:" << std::endl;
    for( std::map<std::string, RuntimeSettings*>::const_iterator it = mSettingObjects.begin(); it != mSettingObjects.end(); ++it )
    {
        std::cout << "- Module: " << it->first << std::endl;
        it->second->printHelp("\t");
        std::cout << std::endl;
    }
    // Print reference to website.
    std::cout << std::endl;
    std::cout << "For more information, please visit our website at " << SMTRAT_WEBSITE << std::endl;
}


/**
 * Print statement of no warranty.
 */
void RuntimeSettingsManager::printWarranty() const 
{
   std::cout << "\
HERE IS NO WARRANTY FOR THE PROGRAM, TO THE EXTENT PERMITTED BY \n\
APPLICABLE LAW.  EXCEPT WHEN OTHERWISE STATED IN WRITING THE COPYRIGHT \n\
HOLDERS AND/OR OTHER PARTIES PROVIDE THE PROGRAM \"AS IS\" WITHOUT WARRANTY \n\
OF ANY KIND, EITHER EXPRESSED OR IMPLIED, INCLUDING, BUT NOT LIMITED TO, \n\
THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR \n\
PURPOSE.  THE ENTIRE RISK AS TO THE QUALITY AND PERFORMANCE OF THE PROGRAM \n\
IS WITH YOU.  SHOULD THE PROGRAM PROVE DEFECTIVE, YOU ASSUME THE COST OF \n\
ALL NECESSARY SERVICING, REPAIR OR CORRECTION. \n";
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
    std::cout << "\
SMT-RAT  Copyright (C) 2012-2013 \n \
Florian Corzilius, Ulrich Loup, Sebastian Junges, Erika Abraham \n\n\
This program comes with ABSOLUTELY NO WARRANTY; for details run the solver with --warranty'. \n\
This is free software, and you are welcome to redistribute it \n\
under certain conditions;"<< std::endl << std::endl;
}

void RuntimeSettingsManager::printInfo() const
{
    std::cout << "Code was compiled with compiler ? , version: " << smtrat::CompileInfo::CXXCompiler << std::endl;
    std::cout << "Build type:" << smtrat::CompileInfo::BuildType << std::endl;   
    std::cout << "Code is based on commit " << smtrat::CompileInfo::GitRevisionSHA1 << ". " << std::endl;
    std::cout << "Build on a " << smtrat::CompileInfo::SystemName << " (" << CompileInfo::SystemVersion << ") machine." << std::endl;
}

}
