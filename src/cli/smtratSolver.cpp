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

#ifndef __WIN
#include <sys/resource.h>
#endif

#ifdef SMTRAT_DEVOPTION_Statistics
#include <smtrat-common/statistics/StatisticsCollector.h>
#include <smtrat-common/statistics/StatisticsPrinter.h>
#include <smtrat-common/statistics/StatisticsSettings.h>
#ifdef TIMING
#include <smtrat-common/statistics/TimingStatistics.h>
#endif // TIMING
#endif //SMTRAT_DEVOPTION_Statistics

#include <smtrat-common/settings/SettingsComponents.h>
#include <smtrat-common/settings/SettingsParser.h>

#include "handle_options.h"
#include "parser/ParserWrapper.h"
#include "parser/ParserSettings.h"
#include <carl-io/SMTLIBStream.h>
#include <carl/util/TimingCollector.h>
#include <carl-logging/logging-internals.h>
#include "tools/config.h"
#include "tools/cnf_conversion.h"
#include "tools/execute_smtlib.h"
#include "tools/Executor.h"
#include "tools/formula_analyzer.h"
#include "tools/parser_dimacs.h"
#include "tools/parser_opb.h"
#include "tools/parser_smtlib.h"
#include "tools/preprocessor.h"


void print_statistics() {
#ifdef SMTRAT_DEVOPTION_Statistics
	#ifdef TIMING
	if (smtrat::settings_solver().print_timings) {
		std::cout << carl::TimingCollector::getInstance() << std::endl;
	}
	smtrat::TimingStatistics& timingStatistics = smtrat::statistics_get<smtrat::TimingStatistics>("Timing");
	timingStatistics.addTimingCollector(carl::TimingCollector::getInstance());
	#endif
	smtrat::StatisticsCollector::getInstance().collect();
	if (smtrat::settings_statistics().print_as_smtlib) {
		std::cout << smtrat::statistics_as_smtlib() << std::endl;
	}
	if (smtrat::settings_statistics().export_as_xml) {
		smtrat::statistics_to_xml_file(smtrat::settings_statistics().xml_filename);
	}
#endif
}

void setup_logging() {
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
}

int main( int argc, char* argv[] )
{
	setup_logging();
	SMTRAT_LOG_DEBUG("smtrat", "Starting smtrat.");

	auto& parser = smtrat::SettingsParser::getInstance();
	smtrat::parser::registerParserSettings(parser);
	#ifdef SMTRAT_DEVOPTION_Statistics
	smtrat::statistics::registerStatisticsSettings(parser);
	#endif
	#ifdef CLI_ENABLE_ANALYZER
	smtrat::analyzer::registerAnalyzerSettings(parser);
	#endif
	smtrat::SettingsComponents::getInstance().add_to_parser(parser);
	parser.finalize();
	parser.parse_options(argc, argv);

	{
		// handle easy options of CoreSettings
		int basic_exitcode = smtrat::handle_basic_options(parser);
		if (basic_exitcode != SMTRAT_EXIT_UNDEFINED) {
			return basic_exitcode;
		}
	}

	int exitCode = 0;
	
	if (smtrat::settings_solver().preprocess) {
		exitCode = smtrat::preprocess_file(smtrat::settings_parser().input_file, smtrat::settings_solver().preprocess_output_file);
	} else if (smtrat::settings_analyzer().enabled) {
		exitCode = smtrat::analyze_file(smtrat::settings_parser().input_file);
	} else if (smtrat::settings_solver().convert_to_cnf_dimacs) {
		exitCode = smtrat::convert_to_cnf_dimacs(smtrat::settings_parser().input_file, smtrat::settings_solver().preprocess_output_file);
	} else if (smtrat::settings_solver().convert_to_cnf_smtlib) {
		exitCode = smtrat::convert_to_cnf_smtlib(smtrat::settings_parser().input_file, smtrat::settings_solver().preprocess_output_file);
	} else {
		SMTRAT_LOG_INFO("smtrat", "Constructing strategy.");

		CMakeStrategySolver strategy;

		if (smtrat::settings_core().show_strategy) {
			strategy.printStrategyGraph();
		}
		if (smtrat::settings_parser().read_dimacs) {
			exitCode = smtrat::run_dimacs_file(strategy, smtrat::settings_parser().input_file);
		} else if (smtrat::settings_parser().read_opb) {
			exitCode = smtrat::run_opb_file(strategy, smtrat::settings_parser().input_file);
		} else {
			// Parse input.
			smtrat::resource::Limiter::getInstance().setTimeoutHandler(&print_statistics);		
			try {

				auto e = smtrat::Executor<CMakeStrategySolver>(strategy);
				exitCode = smtrat::executeFile(smtrat::settings_parser().input_file, e);

				if (is_sat(e.lastAnswer)) {
					if (smtrat::settings_solver().print_all_models) {
						strategy.printAllAssignments(std::cout);
					} else if (smtrat::settings_solver().print_model) {
						strategy.printAssignment();
					}
				}

			} catch (const std::bad_alloc& e) {
				std::raise(ENOMEM);
			}
		}
	}

	print_statistics();

	return exitCode;
}
