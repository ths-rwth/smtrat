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

#include <stdio.h>
#include <string.h>
#include <map>
#include <iostream>

#include "RuntimeSettingsManager.h"
#include "ExitCodes.h"

#include "../lib/config.h"

namespace smtrat {

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
        if( strlen(argv[argi]) > 2 && argv[argi][0] == '-' && argv[argi][1] == '-') 
        {
            std::string optionName(argv[argi+2]);
            // check for global options.
            if(optionName == "help") 
            {
                printHelp();
                exit(SMTRAT_EXIT_SUCCESS);
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
            // no more global options, so we expect module options
            else 
            {
                size_t semicolonPosition(optionName.find(':'));
                // Check if a semicolon was found
                if(semicolonPosition == optionName.npos) 
                {
                    std::cerr << "Unknown option: " << argv[argi] << std::endl;
                    exit(SMTRAT_EXIT_UNEXPECTED_INPUT);
                }
                // Split into  name and keyvalue string.
                std::string settingsObjectName = optionName.substr(0,semicolonPosition);
                std::string keyValueString = optionName.substr(semicolonPosition);
                
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
    std::cout << "Example ./solver --parser:trace example.smt2. Runs the solver on example.smt2 with tracing enabled for the parser." << std::endl;
    std::cout << std::endl;
    // Print help for the global options.
    std::cout << "Global options:" << std::endl;
    std::cout << "\t --help \t\t prints this help." << std::endl;
    std::cout << "\t --warranty \t\t prints the warranty." << std::endl;
    std::cout << std::endl;
    // Print help for all known modules.
    for( std::map<std::string, RuntimeSettings*>::const_iterator it = mSettingObjects.begin(); it != mSettingObjects.end(); ++it )
    {
        std::cout << "Module: " << it->first << std::endl;
        it->second->printHelp("\t");
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

}

        
}
