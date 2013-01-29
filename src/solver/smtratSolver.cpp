/*
 *  SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
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
 * @file smtratSolver.cpp
 * @author Florian Corzilius
 *
 * Created on May 04, 2012, 2:40 PM
 */

#include <iostream>
#include <fstream>
#include "ExitCodes.h"
#include "parser/Driver.h"
#include "../lib/strategies/strategies.h"
#include "parser/ParserSettings.h"
#include "RuntimeSettingsManager.h"
#include "../lib/modules/AddModules.h"
#include "../lib/config.h"

#ifdef GATHER_STATS
#include "../lib/utilities/stats/CollectStatistics.h"
#include "lib/utilities/stats/StatisticSettings.h"
#endif //GATHER_STATS


struct Smt2Options
{
    int statusFlag;
    bool printAssignment;
};

/**
 * Parse the file and save it in formula.
 * @param pathToInputFile The path to the input smt2 file.
 * @param formula A pointer to the formula object which holds the parsed input afterwards.
 * @param options Save options from the smt2 file here.
 */
void parseInput(const std::string& pathToInputFile, smtrat::Formula* formula, smtrat::ParserSettings* settings, Smt2Options& options)
{
    // The parser
    smtrat::Driver   parser( formula );
    settings->setOptionsToParser(parser);
    std::fstream infile( pathToInputFile.c_str() );
    if( !infile.good() )
    {
        std::cerr << "Could not open file: " << pathToInputFile << std::endl;
        exit(SMTRAT_EXIT_NOSUCHFILE);
    }
    bool parsingSuccessful = parser.parse_stream( infile, pathToInputFile.c_str() );
    if(!parsingSuccessful)
    {
        std::cerr << "Parse error" << std::endl;
        exit(SMTRAT_EXIT_PARSERFAILURE);
    }
    options.statusFlag = parser.status();
    options.printAssignment = parser.printAssignment();
}

/**
 * Determine the returnvalue of the process and its output.
 * @param status the parsed statusflag of the smt2 file.
 * @param answer the answer from the solver
 * @return the corresponding returnvalue.
 */
int determineResult(int status, smtrat::Answer answer)
{
    switch( answer )
    {
        case smtrat::True:
        {
            if( status == 0 )
            {
                std::cout << "error, expected unsat, but returned sat" << std::endl;
                return SMTRAT_EXIT_WRONG_ANSWER;
            }
            else
            {
                std::cout << "sat" << std::endl;
                return SMTRAT_EXIT_SAT;
            }
            break;
        }
        case smtrat::False:
        {
            if( status == 1 )
            {
                std::cout << "error, expected sat, but returned unsat" << std::endl;
                return SMTRAT_EXIT_WRONG_ANSWER;
            }
            else
            {
                std::cout << "unsat" << std::endl;
                return SMTRAT_EXIT_UNSAT;
            }
            break;
        }
        case smtrat::Unknown:
        {
            std::cout << "unknown" << std::endl;
            return SMTRAT_EXIT_UNKNOWN;
            break;
        }
        default:
        {
            std::cerr << "Unexpected output!" << std::endl;
            return SMTRAT_EXIT_UNEXPECTED_ANSWER;
        }
    }
}


/**
 *
 */
int main( int argc, char* argv[] )
{
    // This variable will hold the inputfile.
    std::string pathToInputFile = "";
    // This will point to the parsed formula;
    smtrat::Formula* form = new smtrat::Formula( smtrat::AND );

    // Construct solver
    smtrat::NRATSolver* nratSolver = new smtrat::NRATSolver( form );
    std::list<std::pair<std::string, smtrat::RuntimeSettings*> > settingsObjects = smtrat::addModules(nratSolver);

    // Construct the settingsManager
    smtrat::RuntimeSettingsManager settingsManager;
    // Introduce the smtrat core settingsObjects to the manager.
    #ifdef SMTRAT_ENABLE_VALIDATION
    settingsManager.addSettingsObject("validation", smtrat::Module::validationSettings);
    #endif
    // Create and introduce a parser settings object.
    smtrat::ParserSettings* parserSettings = new smtrat::ParserSettings();
    settingsManager.addSettingsObject("parser", parserSettings);
    // Introduce the settingsobject for the statistics to the manager.
    #ifdef GATHER_STATS
    settingsManager.addSettingsObject("stats", smtrat::CollectStatistics::settings);
    #endif
    // Introduce the settingsObjects from the modules to the manager
    settingsManager.addSettingsObject(settingsObjects);

    // Parse commandline;
    pathToInputFile = settingsManager.parseCommandline(argc, argv);

    Smt2Options smt2options;
    // Parse input
    parseInput(pathToInputFile, form, parserSettings, smt2options);


    // Run solver
    smtrat::Answer      answer     = nratSolver->isConsistent();
    // Determine result.
    int returnValue = determineResult(smt2options.statusFlag, answer);
    // Print assignment.
    if(smt2options.printAssignment && answer == smtrat::True)
    {
        std::cout << std::endl;
        nratSolver->printModel( std::cout );
    }
    // Delete the solver and the formula.
    delete nratSolver;
    delete form;
    // Export statistics
    #ifdef GATHER_STATS
    smtrat::CollectStatistics::produceOutput();
    #endif

    return returnValue;
}
