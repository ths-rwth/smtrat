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
#include "parser/Driver.h"
#include "NRATSolver.h"

/**
 *
 */
int main( int argc, char* argv[] )
{
    smtrat::Formula* form = new smtrat::Formula( smtrat::AND );
    smtrat::Driver   driver( form );

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
        else
        {
            // read a file with expressions

            std::fstream infile( argv[ai] );
            if( !infile.good() )
            {
                std::cerr << "Could not open file: " << argv[ai] << std::endl;
                return 0;
            }

            bool result = driver.parse_stream( infile, argv[ai] );
            if( result )
            {
                smtrat::NRATSolver* nratSolver = new smtrat::NRATSolver( form );
                switch( nratSolver->isConsistent() )
                {
                    case smtrat::True:
                    {
                        std::cout << "sat" << std::endl;
                        break;
                    }
                    case smtrat::False:
                    {
                        std::cout << "unsat" << std::endl;
                        break;
                    }
                    case smtrat::Unknown:
                    {
                        std::cout << "unknown" << std::endl;
                        break;
                    }
                    default:
                    {
                        std::cerr << "Unexpected output!" << std::endl;
                    }
                }
                delete nratSolver;
                delete form;
            }
        }
    }
    return (EXIT_SUCCESS);
}
