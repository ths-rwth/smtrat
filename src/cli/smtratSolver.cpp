/**
 * @file smtratSolver.cpp
 * @author Florian Corzilius
 * @author Sebastian Junges
 *
 * Created on May 04, 2012, 2:40 PM
 */

#include "parser/theories/TheoryTypes.h"

#include <iostream>
#include <fstream>
#include "ExitCodes.h"
#include "../lib/config.h"

#include "config.h"
#include "../lib/strategies/config.h"
#include "RuntimeSettingsManager.h"

#ifndef __WIN
#include <sys/resource.h>
#endif
#include "../lib/solver/Module.h"
#include "../lib/Common.h"

#include "../lib/datastructures/unsatcore/UnsatCore.h"

#ifdef SMTRAT_DEVOPTION_Statistics
#include "../lib/utilities/stats/CollectStatistics.h"
#include "lib/utilities/stats/StatisticSettings.h"
#endif //SMTRAT_DEVOPTION_Statistics


#include "parser/ParserWrapper.h"
#include "../lib/Common.h"
#include <carl/formula/parser/DIMACSExporter.h>
#include <carl/formula/parser/DIMACSImporter.h>
#include <carl/formula/parser/OPBImporter.h>
#include <carl/io/SMTLIBStream.h>
#include <carl/util/TimingCollector.h>
#include "tools/Executor.h"

template<typename Executor>
bool parseInput(const std::string& pathToInputFile, Executor* e, bool& queueInstructions) {
	if (pathToInputFile == "-") {
		queueInstructions = false;
		SMTRAT_LOG_DEBUG("smtrat", "Starting to parse from stdin");
		return smtrat::parseSMT2File(e, queueInstructions, std::cin);
	}

	std::ifstream infile(pathToInputFile);
	if (!infile.good()) {
		std::cerr << "Could not open file: " << pathToInputFile << std::endl;
		exit(SMTRAT_EXIT_NOSUCHFILE);
	}
	SMTRAT_LOG_DEBUG("smtrat", "Starting to parse " << pathToInputFile);
	return smtrat::parseSMT2File(e, queueInstructions, infile);
}

/**
 * Parse the file and save it in formula.
 * @param pathToInputFile The path to the input smt2 file.
 * @param formula A pointer to the formula object which holds the parsed input afterwards.
 * @param options Save options from the smt2 file here.
 */
unsigned executeFile(const std::string& pathToInputFile, CMakeStrategySolver* solver, const smtrat::RuntimeSettingsManager& settingsManager) {
#ifdef __WIN
//TODO: do not use magical number
#pragma comment(linker, "/STACK:10000000")
#else
	// Increase stack size to the maximum.
	rlimit rl;
	getrlimit(RLIMIT_STACK, &rl);
	rl.rlim_cur = rl.rlim_max;
	setrlimit(RLIMIT_STACK, &rl);
#endif

	auto e = new smtrat::Executor<CMakeStrategySolver>(solver);
	if (settingsManager.exportDIMACS()) e->exportDIMACS = true;

	bool queueInstructions = true;
	if (!parseInput(pathToInputFile, e, queueInstructions)) {
		std::cerr << "Parse error" << std::endl;
		delete e;
		exit(SMTRAT_EXIT_PARSERFAILURE);
	}
	if (queueInstructions) {
		if (e->hasInstructions()) {
			SMTRAT_LOG_WARN("smtrat", "Running queued instructions.");
			e->runInstructions();
		} else {
			SMTRAT_LOG_WARN("smtrat", "Did not parse any instructions.");
		}
	}
	unsigned exitCode = e->getExitCode();
	if (e->lastAnswer == smtrat::Answer::SAT) {
		if (settingsManager.printModel()) solver->printAssignment();
		else if (settingsManager.printAllModels()) solver->printAllAssignments(std::cout);
	}
        else if(e->lastAnswer == smtrat::Answer::UNKNOWN) {
            if (settingsManager.printInputSimplified())
            {
                smtrat::FormulaT formula = solver->getInputSimplified().second;
				auto smtrepr = carl::outputSMTLIB(solver->logic(), { formula });

                if( settingsManager.simplifiedInputFileName() == "" )
                    e->regular() << smtrepr;
                else
                {
                    std::ofstream file;
                    file.open(settingsManager.simplifiedInputFileName());
                    file << smtrepr;
                    file.close();
                }
            }
        }
	delete e;
	return exitCode;
}

void printTimings(smtrat::Manager* solver)
{
    std::cout << "**********************************************" << std::endl;
    std::cout << "*                  Timings                   *" << std::endl;
    std::cout << "**********************************************" << std::endl;
    std::cout << "\t\tAdd \t\tCheck \t (calls) \tRemove" << std::endl;
    for(std::vector<smtrat::Module*>::const_iterator it =  solver->getAllGeneratedModules().begin(); it != solver->getAllGeneratedModules().end(); ++it)
    {
        std::cout << (*it)->moduleName() << ":\t" << (*it)->getAddTimerMS() << "\t\t" << (*it)->getCheckTimerMS() << "\t(" << (*it)->getNrConsistencyChecks() << ")\t\t" << (*it)->getRemoveTimerMS() << std::endl;

    }
    std::cout << "**********************************************" << std::endl;
}

//#include "../lib/datastructures/expression/ExpressionTest.h"

/**
 *
 */
int main( int argc, char* argv[] )
{
	//smtrat::testExpression();
#ifdef LOGGING
	if (!carl::logging::logger().has("smtrat")) {
		carl::logging::logger().configure("smtrat", "smtrat.log");
	}
	if (!carl::logging::logger().has("stdout")) {
		carl::logging::logger().configure("stdout", std::cout);
	}
	//carl::logging::logger().formatter("stdout")->printInformation = false;
	carl::logging::logger().filter("smtrat")
		("smtrat", carl::logging::LogLevel::LVL_INFO)
		("smtrat.cad", carl::logging::LogLevel::LVL_DEBUG)
		("smtrat.preprocessing", carl::logging::LogLevel::LVL_DEBUG)
	;
	carl::logging::logger().filter("stdout")
		("smtrat", carl::logging::LogLevel::LVL_DEBUG)
		("smtrat.module", carl::logging::LogLevel::LVL_INFO)
		("smtrat.parser", carl::logging::LogLevel::LVL_INFO)
		("smtrat.cad", carl::logging::LogLevel::LVL_INFO)
		("smtrat.nlsat.rootindexer", carl::logging::LogLevel::LVL_INFO)
		("smtrat.nlsat.assignmentfinder", carl::logging::LogLevel::LVL_INFO)
		("smtrat.preprocessing", carl::logging::LogLevel::LVL_DEBUG)
		("smtrat.strategygraph", carl::logging::LogLevel::LVL_DEBUG)
	;
	carl::logging::logger().formatter("stdout")->printInformation = true;
#endif
	SMTRAT_LOG_INFO("smtrat", "Starting smtrat.");
    // This variable will hold the input file.
    std::string pathToInputFile = "";

    // Construct the settingsManager.
    smtrat::RuntimeSettingsManager settingsManager;
    // Introduce the smtrat core settingsObjects to the manager.
    #ifdef SMTRAT_DEVOPTION_Validation
    settingsManager.addSettingsObject( "validation", smtrat::Module::validationSettings );
    #endif
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

    if( settingsManager.printStrategy() )
    {
        solver->printStrategyGraph();
        delete solver;
        return (int)SMTRAT_EXIT_SUCCESS;
    }

    #ifdef SMTRAT_DEVOPTION_Statistics
    //smtrat::CollectStatistics::settings->rOutputChannel().rdbuf( parser.rDiagnosticOutputChannel().rdbuf() );
    #endif

    // Introduce the settingsObjects from the modules to the manager.
    //settingsManager.addSettingsObject( settingsObjects );
    //settingsObjects.clear();


	unsigned exitCode = 0;
	if (settingsManager.readDIMACS()) {
		carl::DIMACSImporter<smtrat::Poly> dimacs(pathToInputFile);
		while (dimacs.hasNext()) {
			solver->add(dimacs.next());
			switch (solver->check()) {
				case smtrat::Answer::SAT: {
					std::cout << "sat" << std::endl;
					exitCode = SMTRAT_EXIT_SAT;
					break;
				}
				case smtrat::Answer::UNSAT: {
					std::cout << "unsat" << std::endl;
					exitCode = SMTRAT_EXIT_UNSAT;
					break;
				}
				case smtrat::Answer::UNKNOWN: {
					std::cout << "unknown" << std::endl;
					exitCode = SMTRAT_EXIT_UNKNOWN;
					break;
				}
				default: {
					std::cerr << "unexpected output!";
					exitCode = SMTRAT_EXIT_UNEXPECTED_ANSWER;
					break;
				}
			}
			if (dimacs.hasNext()) solver->reset();
		}
	} else if (settingsManager.readOPB()) {
		carl::OPBImporter<smtrat::Poly> opb(pathToInputFile);
		SMTRAT_LOG_INFO("smtrat", "Parsing " << pathToInputFile << " using OPB");
		auto input = opb.parse();
		if (!input) {
			SMTRAT_LOG_ERROR("smtrat", "Parsing " << pathToInputFile << " failed.");
			exitCode = SMTRAT_EXIT_UNKNOWN;
		} else {
			SMTRAT_LOG_INFO("smtrat", "Parsed " << input->first);
			SMTRAT_LOG_INFO("smtrat", "with objective " << input->second);
			if (!input->second.isConstant()) {
				solver->addObjective(input->second, true);
			}
			solver->add(input->first);
			switch (solver->check()) {
				case smtrat::Answer::SAT: {
					std::cout << "sat" << std::endl;
					exitCode = SMTRAT_EXIT_SAT;
					break;
				}
				case smtrat::Answer::UNSAT: {
					std::cout << "unsat" << std::endl;
					exitCode = SMTRAT_EXIT_UNSAT;
					break;
				}
				case smtrat::Answer::UNKNOWN: {
					std::cout << "unknown" << std::endl;
					exitCode = SMTRAT_EXIT_UNKNOWN;
					break;
				}
				default: {
					std::cerr << "unexpected output!";
					exitCode = SMTRAT_EXIT_UNEXPECTED_ANSWER;
					break;
				}
			}
		}
	} else {
		// Parse input.
		try {
			exitCode = executeFile(pathToInputFile, solver, settingsManager);
		} catch (const std::bad_alloc& e) {
			std::raise(ENOMEM);
		}
	}

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

	#ifdef TIMING
	std::cout << carl::TimingCollector::getInstance() << std::endl;
	#endif


    // Delete the solver and the formula.
    delete solver;

    return (int)exitCode;
}
