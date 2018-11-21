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
#include <smtrat-common/smtrat-common.h>
#include "ExitCodes.h"

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
#include <carl/io/SMTLIBStream.h>
#include <carl/util/TimingCollector.h>
#include "tools/Executor.h"
#include "parse_input.h"
#include "tools/dimacs.h"
#include "tools/pseudoboolean.h"


void printTimings(smtrat::Manager& solver)
{
    std::cout << "**********************************************" << std::endl;
    std::cout << "*                  Timings                   *" << std::endl;
    std::cout << "**********************************************" << std::endl;
    std::cout << "\t\tAdd \t\tCheck \t (calls) \tRemove" << std::endl;
    for(std::vector<smtrat::Module*>::const_iterator it =  solver.getAllGeneratedModules().begin(); it != solver.getAllGeneratedModules().end(); ++it)
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
    CMakeStrategySolver strategy;

    if( settingsManager.printStrategy() )
    {
        strategy.printStrategyGraph();
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
		exitCode = smtrat::run_dimacs_file(strategy, pathToInputFile);
	} else if (settingsManager.readOPB()) {
		exitCode = smtrat::run_opb_file(strategy, pathToInputFile);
	} else {
		// Parse input.
		try {

			auto e = smtrat::Executor<CMakeStrategySolver>(strategy);
			if (settingsManager.exportDIMACS()) e.exportDIMACS = true;
			exitCode = smtrat::executeFile(pathToInputFile, e, settingsManager);

			if (e.lastAnswer == smtrat::Answer::SAT) {
			if (settingsManager.printModel()) strategy.printAssignment();
			else if (settingsManager.printAllModels()) strategy.printAllAssignments(std::cout);
			}
			else if(e.lastAnswer == smtrat::Answer::UNKNOWN) {
			if (settingsManager.printInputSimplified())
			{
				smtrat::FormulaT formula = strategy.getInputSimplified().second;
				auto smtrepr = carl::outputSMTLIB(strategy.logic(), { formula });

				if( settingsManager.simplifiedInputFileName() == "" )
					e.regular() << smtrepr;
				else
				{
					std::ofstream file;
					file.open(settingsManager.simplifiedInputFileName());
					file << smtrepr;
					file.close();
				}
			}
			}

		} catch (const std::bad_alloc& e) {
			std::raise(ENOMEM);
		}
	}

    if( settingsManager.doPrintTimings() )
    {
        printTimings( strategy );
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

    return (int)exitCode;
}
