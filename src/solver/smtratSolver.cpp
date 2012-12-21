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
#include "../lib/NRATSolver.h"

#ifdef GATHER_STATS

#include "../lib/utilities/stats/CollectStatistics.h"

#endif //GATHER_STATS

/**
 *
 */
int main( int argc, char* argv[] )
{
    // Call the sighandler code on user abort
    // TODO update we should use sigaction() 
    //signal(SIGINT, &sighandler);

    smtrat::Formula* form = new smtrat::Formula( smtrat::AND );
    smtrat::Driver   driver( form );

    bool printStats = false;
    bool exportStats = false;
    std::string pathToStatsXML;
    

    if( argc == 1 )
    {
        std::cout << "This is " << SMTRAT_PROJECT_NAME << "." << std::endl;
        std::cout << "Version: " << SMTRAT_VERSION << std::endl;
        std::cout << "For more information, run this binary with --help." << std::endl;
    }
    int returnValue = SMTRAT_EXIT_USERABORT;
    for( int ai = 1; ai < argc; ++ai )
    {
        if( argv[ai] == std::string( "-p" ) )
        {
            driver.trace_parsing = true;
        }
        else if( argv[ai] == std::string( "-s" ) )
        {
            driver.trace_scanning = true;
        }
        else if( argv[ai] == std::string( "--print-stats") ) {
            #ifdef GATHER_STATS
            printStats = true;
            #endif
        }
        else if( argv[ai] == std::string( "--export-stats") ) {
            #ifdef GATHER_STATS
            exportStats = true;
            #endif
            //TODO make this optional.
            pathToStatsXML = argv[++ai];
        }
        else if( argv[ai] == std::string( "--gb-info") )
        {
            std::cout << "Groebner module settings: GBModuleSettings" << std::endl;
        }
        else if( argv[ai] == std::string( "--help") ) {
            std::cout << "The help is not yet implemented. Please visit our website ...." << std::endl;
        }
        else
        {
            // read a file with expressions

            std::fstream infile( argv[ai] );
            if( !infile.good() )
            {
                std::cerr << "Could not open file: " << argv[ai] << std::endl;
                return SMTRAT_EXIT_UNEXPECTED_INPUT;
            }

            bool result = driver.parse_stream( infile, argv[ai] );
            if( result )
            {
                smtrat::NRATSolver* nratSolver = new smtrat::NRATSolver( form );
                smtrat::Answer      answer     = nratSolver->isConsistent();
                switch( answer )
                {
                    case smtrat::True:
                    {
                        if( driver.status == 0 )
                        {
                            std::cout << "error, expected unsat, but returned sat" << std::endl;
                            returnValue = SMTRAT_EXIT_WRONG_ANSWER;
                        }
                        else
                        {
                            std::cout << "sat" << std::endl;
                            returnValue = SMTRAT_EXIT_SAT;
                        }
                        break;
                    }
                    case smtrat::False:
                    {
                        if( driver.status == 1 )
                        {
                            std::cout << "error, expected sat, but returned unsat" << std::endl;
                            returnValue = SMTRAT_EXIT_WRONG_ANSWER;
                        }
                        else
                        {
                            std::cout << "unsat" << std::endl;
                            returnValue = SMTRAT_EXIT_UNSAT;
                        }
                        break;
                    }
                    case smtrat::Unknown:
                    {
                        std::cout << "unknown" << std::endl;
                        returnValue = SMTRAT_EXIT_UNKNOWN;
                        break;
                    }
                    default:
                    {
                        std::cerr << "Unexpected output!" << std::endl;
                        returnValue = SMTRAT_EXIT_UNEXPECTED_ANSWER;
                    }
                }
                if( driver.printAssignment && answer == smtrat::True )
                {
                    std::cout << std::endl;
                    nratSolver->printModel( std::cout );
                }
                delete nratSolver;
                delete form;

                #ifdef GATHER_STATS
                if( printStats )
                {
                    smtrat::CollectStatistics::print( std::cout );
                }
                if( exportStats )
                {
                    smtrat::CollectStatistics::exportXML(pathToStatsXML);
                }
                #endif //GATHER_STATS
            }
            else
            {
                std::cerr << "Parse error" << std::endl;
                returnValue = SMTRAT_EXIT_PARSERFAILURE;
            }
        }
    }
    return returnValue;
}
