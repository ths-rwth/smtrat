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
 * @author Sebastian Junges
 *
 * Created on May 04, 2012, 2:40 PM
 */

#include <iostream>
#include <fstream>
#include "ExitCodes.h"
#include "../lib/config.h"

#include "config.h"
#include "parser/Driver.h"
#include CMakeStrategyHeader
#include "parser/ParserSettings.h"
#include "RuntimeSettingsManager.h"
#include "../lib/modules/AddModules.h"

#ifdef SMTRAT_DEVOPTION_Statistics
#include "../lib/utilities/stats/CollectStatistics.h"
#include "lib/utilities/stats/StatisticSettings.h"
#endif //SMTRAT_DEVOPTION_Statistics

/**
 * Parse the file and save it in formula.
 * @param pathToInputFile The path to the input smt2 file.
 * @param formula A pointer to the formula object which holds the parsed input afterwards.
 * @param options Save options from the smt2 file here.
 */
void parseInput( const std::string& pathToInputFile, smtrat::Driver& _parser, smtrat::ParserSettings* settings )
{
    settings->setOptionsToParser( _parser );
    std::fstream infile( pathToInputFile.c_str() );
    if( !infile.good() )
    {
        std::cerr << "Could not open file: " << pathToInputFile << std::endl;
        exit(SMTRAT_EXIT_NOSUCHFILE);
    }
    bool parsingSuccessful = _parser.parse_stream( infile, pathToInputFile.c_str() );
    if(!parsingSuccessful)
    {
        std::cerr << "Parse error" << std::endl;
        exit(SMTRAT_EXIT_PARSERFAILURE);
    }
}

void printTimings(smtrat::Manager* solver)
{
    std::cout << "**********************************************" << std::endl;
    std::cout << "*                  Timings                   *" << std::endl;
    std::cout << "**********************************************" << std::endl;
    std::cout << "\t\tAdd \t\tCheck \t (calls) \tRemove" << std::endl;
    for(std::vector<smtrat::Module*>::const_iterator it =  solver->getAllGeneratedModules().begin(); it != solver->getAllGeneratedModules().end(); ++it)
    {
        std::cout << smtrat::moduleTypeToString((*it)->type()) << ":\t" << (*it)->getAddTimerMS() << "\t\t" << (*it)->getCheckTimerMS() << "\t(" << (*it)->getNrConsistencyChecks() << ")\t\t" << (*it)->getRemoveTimerMS() << std::endl;

    }
    std::cout << "**********************************************" << std::endl;
}


/**
 *
 */
int main( int argc, char* argv[] )
{   
    // This variable will hold the input file.
    std::string pathToInputFile = "";

    // Construct the settingsManager.
    smtrat::RuntimeSettingsManager settingsManager;
    // Introduce the smtrat core settingsObjects to the manager.
    #ifdef SMTRAT_DEVOPTION_Validation
    settingsManager.addSettingsObject( "validation", smtrat::Module::validationSettings );
    #endif
    // Create and introduce a parser settings object.
    smtrat::ParserSettings* parserSettings = new smtrat::ParserSettings();
    settingsManager.addSettingsObject( "parser", parserSettings );
    // Introduce the settings object for the statistics to the manager.
    #ifdef SMTRAT_DEVOPTION_Statistics
    settingsManager.addSettingsObject("stats", smtrat::CollectStatistics::settings);
    #endif

    // Parse command line.
    pathToInputFile = settingsManager.parseCommandline( argc, argv );

    // Parse input.
    smtrat::Driver parser;
    parseInput( pathToInputFile, parser, parserSettings );
    
    // Construct solver.
    CMakeStrategySolver* nratSolver = new CMakeStrategySolver();
    nratSolver->rDebugOutputChannel().rdbuf( parser.rDiagnosticOutputChannel().rdbuf() );
    std::list<std::pair<std::string, smtrat::RuntimeSettings*> > settingsObjects = smtrat::addModules( nratSolver );
    
    // Introduce the settingsObjects from the modules to the manager.
    settingsManager.addSettingsObject( settingsObjects );

    // Apply parsed instruction.
    int returnValue = 0;
    smtrat::Answer lastAnswer = smtrat::Unknown;
    smtrat::InstructionKey currentInstructionKey;
    smtrat::InstructionValue currentInstructionValue;
    while( parser.getInstruction( currentInstructionKey, currentInstructionValue ) )
    {
        switch( currentInstructionKey )
        {
            case smtrat::PUSHBT:
            {
                for( int i = 0; i<currentInstructionValue.num; ++i )
                    nratSolver->push();
                break;
            }
            case smtrat::POPBT:
            {
                for( int i = 0; i<currentInstructionValue.num; ++i )
                    if( !nratSolver->pop() )
                        parser.error( "Cannot pop an empty stack of backtrack points!", true );
                break;
            }
            case smtrat::ASSERT:
            {
                nratSolver->add( currentInstructionValue.formula );
                break;
            }
            case smtrat::CHECK:
            {
                lastAnswer = nratSolver->check();
                switch( lastAnswer )
                {
                    case smtrat::True:
                    {
                        if( parser.status() == 0 )
                        {
                            parser.error( "expected unsat, but returned sat", true );
                            returnValue = SMTRAT_EXIT_WRONG_ANSWER;
                        }
                        else
                        {
                            parser.rRegularOutputChannel() << "sat" << std::endl;
                            returnValue = SMTRAT_EXIT_SAT;
                        }
                        break;
                    }
                    case smtrat::False:
                    {
                        if( parser.status() == 1 )
                        {
                            parser.error( "error, expected sat, but returned unsat", true );
                            returnValue = SMTRAT_EXIT_WRONG_ANSWER;
                        }
                        else
                        {
                            parser.rRegularOutputChannel() << "unsat" << std::endl;
                            returnValue = SMTRAT_EXIT_UNSAT;
                        }
                        break;
                    }
                    case smtrat::Unknown:
                    {
                        parser.rRegularOutputChannel() << "unknown" << std::endl;
                        returnValue = SMTRAT_EXIT_UNKNOWN;
                        break;
                    }
                    default:
                    {
                        parser.error( "Unexpected output!", true );
                        returnValue = SMTRAT_EXIT_UNEXPECTED_ANSWER;
                    }
                }
                break;
            }
            case smtrat::GET_ASSIGNMENT:
            {
                if( lastAnswer == smtrat::True )
                {
                    nratSolver->printAssignment( parser.rRegularOutputChannel() );
                }
                break;
            }
            case smtrat::GET_ASSERTS:
            {
                nratSolver->printAssertions( parser.rRegularOutputChannel() );
                break;
            }
            case smtrat::GET_UNSAT_CORE:
            {
                nratSolver->printInfeasibleSubset( parser.rRegularOutputChannel() );
                break;
            }
            default:
            {
                parser.error( "Unknown order!" );
                assert( false );
            }
        }
    }
    
    // Print assignment if provoked by system call.
    if( settingsManager.printModel() && lastAnswer == smtrat::True )
    {
        std::cout << std::endl;
        nratSolver->printAssignment( std::cout );
    }

    if( settingsManager.doPrintTimings() )
    {
        printTimings( nratSolver );
    }
    // Delete the solver and the formula.
    delete nratSolver;
    delete parserSettings;
    // Export statistics.
    #ifdef SMTRAT_DEVOPTION_Statistics
    smtrat::CollectStatistics::produceOutput();
    #endif

    return returnValue;
}
