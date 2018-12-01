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
#include <smtrat-strategies/smtrat-strategies.h>
#include "RuntimeSettingsManager.h"

#ifndef __WIN
#include <sys/resource.h>
#endif
#include <smtrat-modules/Module.h>
#include "../lib/Common.h"

#ifdef SMTRAT_DEVOPTION_Statistics
#include "../lib/utilities/stats/CollectStatistics.h"
#include "lib/utilities/stats/StatisticSettings.h"
#endif //SMTRAT_DEVOPTION_Statistics

#include <smtrat-common/settings/SettingsParser.h>

#include "handle_options.h"
#include "parser/ParserWrapper.h"
#include "../lib/Common.h"
#include <carl/formula/parser/DIMACSExporter.h>
#include <carl/io/SMTLIBStream.h>
#include <carl/util/TimingCollector.h>
#include "tools/Executor.h"
#include "parse_input.h"
#include "tools/dimacs.h"
#include "tools/pseudoboolean.h"
#include "tools/preprocessor.h"



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

	smtrat::SettingsParser parser;
	parser.parse_options(argc, argv);
	const auto& settings = smtrat::Settings();

	{
		// handle easy options of CoreSettings
		int basic_exitcode = smtrat::handle_basic_options(parser);
		if (basic_exitcode != SMTRAT_EXIT_UNDEFINED) {
			return basic_exitcode;
		}
	}

    // This variable will hold the input file.
    std::string pathToInputFile = "";

    // Construct the settingsManager.
    smtrat::RuntimeSettingsManager settingsManager;
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

	if (settings.solver.print_strategy) {
		strategy.printStrategyGraph();
		return SMTRAT_EXIT_SUCCESS;
	}

    #ifdef SMTRAT_DEVOPTION_Statistics
    //smtrat::CollectStatistics::settings->rOutputChannel().rdbuf( parser.rDiagnosticOutputChannel().rdbuf() );
    #endif

    // Introduce the settingsObjects from the modules to the manager.
    //settingsManager.addSettingsObject( settingsObjects );
    //settingsObjects.clear();


	int exitCode = 0;
	if (settings.parser.read_dimacs) {
		exitCode = smtrat::run_dimacs_file(strategy, settings.parser.input_file);
	} else if (settings.parser.read_opb) {
		exitCode = smtrat::run_opb_file(strategy, settings.parser.input_file);
	} else if (settings.solver.preprocess) {
		exitCode = smtrat::preprocess_file(settings.parser.input_file, settings.solver.preprocess_output_file);
	} else {
		// Parse input.
		try {

			auto e = smtrat::Executor<CMakeStrategySolver>(strategy);
			if (settingsManager.exportDIMACS()) e.exportDIMACS = true;
			exitCode = smtrat::executeFile(pathToInputFile, e);

			if (e.lastAnswer == smtrat::Answer::SAT) {
			if (settingsManager.printModel()) strategy.printAssignment();
			else if (settingsManager.printAllModels()) strategy.printAllAssignments(std::cout);
			}

		} catch (const std::bad_alloc& e) {
			std::raise(ENOMEM);
		}
	}

	if (settings.solver.print_timings) {
		smtrat::options_detail::print_timings(strategy);
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

    return exitCode;
}
