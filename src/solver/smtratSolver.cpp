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
#include <sys/resource.h>
#include "ExitCodes.h"
#include "../lib/config.h"

#include "config.h"
#include CMakeStrategyHeader
#include "parser/ParserSettings.h"
#include "RuntimeSettingsManager.h"
#include "../lib/modules/AddModules.h"

#ifdef SMTRAT_DEVOPTION_Statistics
#include "../lib/utilities/stats/CollectStatistics.h"
#include "lib/utilities/stats/StatisticSettings.h"
#endif //SMTRAT_DEVOPTION_Statistics

#define NEWPARSER

#ifdef NEWPARSER

#include "newparser/Parser.h"

class Executor : public smtrat::parser::SMTLIBParser::InstructionHandler {
	CMakeStrategySolver* solver;
	unsigned exitCode;
public:
	smtrat::Answer lastAnswer;
	Executor(CMakeStrategySolver* solver) : smtrat::parser::SMTLIBParser::InstructionHandler(), solver(solver) {}
	void add(const smtrat::Formula* f) {
		this->solver->add(f);
	}
	void check() {
		this->lastAnswer = this->solver->check();
		switch (this->lastAnswer) {
			case smtrat::Answer::True: {
				if (this->infos.has<std::string>("status") && this->infos.get<std::string>("status") == "unsat") {
					error() << "expected unsat, but returned sat";
					this->exitCode = SMTRAT_EXIT_WRONG_ANSWER;
				} else {
					regular() << "sat" << std::endl;
					this->exitCode = SMTRAT_EXIT_SAT;
				}
				//if (settingsManager.printModel()) this->solver->printAssignment(std::cout);
				break;
			}
			case smtrat::Answer::False: {
				if (this->infos.has<std::string>("status") && this->infos.get<std::string>("status") == "sat") {
					error() << "expected sat, but returned unsat";
					this->exitCode = SMTRAT_EXIT_WRONG_ANSWER;
				} else {
					regular() << "unsat" << std::endl;
					this->exitCode = SMTRAT_EXIT_UNSAT;
				}
				break;
			}
			case smtrat::Answer::Unknown: {
				regular() << "unknown";
				this->exitCode = SMTRAT_EXIT_UNKNOWN;
				break;
			}
			default: {
				error() << "unexpected output!";
				this->exitCode = SMTRAT_EXIT_UNEXPECTED_ANSWER;
				break;
			}
		}
	}
	void declareSort(const std::string&, const unsigned&) {
		error() << "(declare-sort <name> <arity>) is not implemented.";
	}
	void defineSort(const std::string&, const std::vector<std::string>&, const std::string&) {
		error() << "(define-sort <name> <sort>) is not implemented.";
	}
	void exit() {
	}
	void getAssertions() {
		this->solver->printAssertions(std::cout);
	}
	void getAssignment() {
		if (this->lastAnswer == smtrat::True) {
			this->solver->printAssignment(std::cout);
		}
	}
	void getProof() {
		error() << "(get-proof) is not implemented.";
	}
	void getUnsatCore() {
		this->solver->printInfeasibleSubset(std::cout);
	}
	void getValue(const std::vector<carl::Variable>&) {
		error() << "(get-value <variables>) is not implemented.";
	}
	void pop(const unsigned& n) {
		for (unsigned i = 0; i < n; i++) this->solver->pop();
	}
	void push(const unsigned& n) {
		for (unsigned i = 0; i < n; i++) this->solver->push();
	}
	void setLogic(const smtrat::Logic& logic) {
		if (this->solver->logic() != smtrat::Logic::UNDEFINED) {
			error() << "The logic has already been set!";
		} else {
			this->solver->rLogic() = logic;
		}
	}
	unsigned getExitCode() const {
		return this->exitCode;
	}
};

/**
 * Parse the file and save it in formula.
 * @param pathToInputFile The path to the input smt2 file.
 * @param formula A pointer to the formula object which holds the parsed input afterwards.
 * @param options Save options from the smt2 file here.
 */
unsigned executeFile(const std::string& pathToInputFile, smtrat::ParserSettings* settings, CMakeStrategySolver* solver, const smtrat::RuntimeSettingsManager& settingsManager) {

	// Increase stack size to the maximum.
	rlimit rl;
	getrlimit(RLIMIT_STACK, &rl);
	rl.rlim_cur = rl.rlim_max;
	setrlimit(RLIMIT_STACK, &rl);

    std::ifstream infile(pathToInputFile);
    if (!infile.good()) {
        std::cerr << "Could not open file: " << pathToInputFile << std::endl;
        exit(SMTRAT_EXIT_NOSUCHFILE);
    }
	Executor* e = new Executor(solver);
	smtrat::parser::SMTLIBParser parser(e, true);
    settings->setOptionsToParser(parser);
    bool parsingSuccessful = parser.parse(infile, pathToInputFile);
	if (parser.queueInstructions) e->runInstructions();
	unsigned exitCode = e->getExitCode();
    if (!parsingSuccessful) {
        std::cerr << "Parse error" << std::endl;
		delete e;
        exit(SMTRAT_EXIT_PARSERFAILURE);
    }
    if( settingsManager.printModel() && e->lastAnswer == smtrat::True )
    {
        std::cout << std::endl;
        solver->printAssignment( std::cout );
    }
	delete e;
	return exitCode;
}

#else

unsigned executeFile(const std::string& pathToInputFile, smtrat::ParserSettings* settings, CMakeStrategySolver* nratSolver, const smtrat::RuntimeSettingsManager& settingsManager) {
	smtrat::Driver parser;
	settings->setOptionsToParser( parser );
    std::fstream infile( pathToInputFile.c_str() );
    if( !infile.good() )
    {
        std::cerr << "Could not open file: " << pathToInputFile << std::endl;
        return SMTRAT_EXIT_NOSUCHFILE;
    }
    bool parsingSuccessful = parser.parse_stream( infile, pathToInputFile.c_str() );
    if(!parsingSuccessful)
    {
        std::cerr << "Parse error" << std::endl;
        return SMTRAT_EXIT_PARSERFAILURE;
    }
	
	nratSolver->rDebugOutputChannel().rdbuf( parser.rDiagnosticOutputChannel().rdbuf() );
	
	unsigned returnValue = 0;
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
	
	return returnValue;
}

#endif

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
    
    #ifdef SMTRAT_DEVOPTION_Statistics
    smtrat::CollectStatistics::settings->setPrintStats( settingsManager.printStatistics() );
    #endif

    // Construct solver.
    CMakeStrategySolver* solver = new CMakeStrategySolver();
	
    std::list<std::pair<std::string, smtrat::RuntimeSettings*> > settingsObjects = smtrat::addModules( solver );
    
    #ifdef SMTRAT_DEVOPTION_Statistics
    //smtrat::CollectStatistics::settings->rOutputChannel().rdbuf( parser.rDiagnosticOutputChannel().rdbuf() );
    #endif
    
    // Introduce the settingsObjects from the modules to the manager.
    settingsManager.addSettingsObject( settingsObjects );
	
	// Parse input.
    unsigned exitCode = executeFile(pathToInputFile, parserSettings, solver, settingsManager);

    if( settingsManager.doPrintTimings() )
    {
        printTimings( solver );
    }
    
    #ifdef SMTRAT_DEVOPTION_Statistics
    smtrat::CollectStatistics::collect();
    smtrat::CollectStatistics::print( true );
    #endif
        
    #ifdef SMTRAT_DEVOPTION_Statistics
    // Export statistics.
    smtrat::CollectStatistics::exportXML();
    #endif
    
    
    // Delete the solver and the formula.
    delete solver;
    delete parserSettings;

	return (int)exitCode;
}
