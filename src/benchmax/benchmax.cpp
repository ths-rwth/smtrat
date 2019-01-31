/**
 * @file benchmax.cpp
 *
 * @author Sebastian Junges
 * @author Ulrich Loup
 *
 * @since 2012-02-01
 * @version 2013-04-23
 */

#include <filesystem>
#include <iostream>
#include "../cli/config.h"
#include "config.h"
namespace fs = std::filesystem;

#include <csignal>

#include "logging.h"
#include "BenchmarkSet.h"
#include "tools/Tools.h"
#include "settings/Settings.h"
#include "settings/SettingsParser.h"
#include "Stats.h"

#include "backends/Backends.h"

using namespace benchmax;

namespace po = boost:: program_options;

const std::string COPYRIGHT =
	"Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Sebastian Junges, Erika Abraham\r\nThis program comes with ABSOLUTELY NO WARRANTY.\r\nThis is free software, and you are welcome to redistribute it \r\nunder certain conditions; use the command line argument --disclaimer in order to get the conditions and warranty disclaimer.";
const std::string WARRANTY =
	"THERE IS NO WARRANTY FOR THE PROGRAM, TO THE EXTENT PERMITTED BY APPLICABLE LAW. EXCEPT WHEN OTHERWISE STATED IN WRITING THE COPYRIGHT HOLDERS AND/OR OTHER PARTIES PROVIDE THE PROGRAM “AS IS” WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESSED OR IMPLIED, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE. THE ENTIRE RISK AS TO THE QUALITY AND PERFORMANCE OF THE PROGRAM IS WITH YOU. SHOULD THE PROGRAM PROVE DEFECTIVE, YOU ASSUME THE COST OF ALL NECESSARY SERVICING, REPAIR OR CORRECTION.";

void printWelcome()
{
	std::cout << "\tSMT-LIB 3.0 Benchmark Tool " << std::endl;
	std::cout << "Support: Florian Corzilius <florian.corzilius@rwth-aachen.de> and Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>" << std::endl;
	std::cout <<  std::endl;
	std::cout << "Usage: Start the tool with the command line argument --help to get further information." << std::endl;
	std::cout << "Examples: ./benchmax -T 90 -D smtlib/qf_nra/etcs/ -D smtlib/qf_nra/bouncing_ball/ -S smtratSolver" << std::endl;
	std::cout << "          ./benchmax -T 90 -D smtlib/qf_nra/etcs/ -D smtlib/qf_nra/bouncing_ball/ -Z z3" << std::endl;
	std::cout << "          ./benchmax -T 90 -D smtlib/qf_nra/etcs/ -D smtlib/qf_nra/bouncing_ball/ --redlog_rlqe /usr/bin/redcsl" << std::endl;
}

bool initApplication(int argc, char** argv) {
	
	carl::logging::logger().configure("stdout", std::cout);
	carl::logging::logger().filter("stdout")
		("benchmax", carl::logging::LogLevel::LVL_INFO)
		("benchmax.ssh", carl::logging::LogLevel::LVL_WARN)
		("benchmax.benchmarks", carl::logging::LogLevel::LVL_INFO)
	;
	carl::logging::logger().resetFormatter();

	auto& parser = SettingsParser::getInstance();
	benchmax::registerSlurmBackendSettings(parser);
	benchmax::registerSSHBackendSettings(parser);
	parser.finalize();
	parser.parse_options(argc, argv);

	if (settings_core().show_help) {
		std::cout << parser.print_help() << std::endl;
		return false;
	}
	if (settings_core().show_settings) {
		std::cout << parser.print_options() << std::endl;
		return false;
	}
	if (settings_core().be_quiet) {
		carl::logging::logger().filter("stdout")
			("benchmax", carl::logging::LogLevel::LVL_INFO)
			("benchmax.backend", carl::logging::LogLevel::LVL_INFO)
			("benchmax.benchmarks", carl::logging::LogLevel::LVL_DEBUG)
		;
	}
	if (settings_core().be_verbose) {
		carl::logging::logger().filter("stdout")
			("benchmax", carl::logging::LogLevel::LVL_DEBUG)
			("benchmax.backend", carl::logging::LogLevel::LVL_DEBUG)
			("benchmax.benchmarks", carl::logging::LogLevel::LVL_DEBUG)
		;
	}

	if (settings_operation().convert_ods_filename != "") {
		std::string filename = settings_operation().convert_ods_filename;
		std::string filter = settings_operation().convert_ods_filter;
		BENCHMAX_LOG_INFO("benchmax.convert", "Converting " << filename << " to ods using import filer " << filter);
		std::stringstream ss;
		ss << "libreoffice --headless --infilter=" << filter << " --convert-to ods " << filename;
		system(ss.str().c_str());
		return false;
	}
	
	
	//if(s.has("compose")) {
	//	Stats::composeStats(s.composeFiles);
	//	return false;
	//}
	//else if(Settings::ProduceLatex)
	//{
	//	Stats::createStatsCompose(settings_benchmarks().output_dir + "latexCompose.xsl");
	//	system(
	//	std::string("xsltproc -o " + settings_benchmarks().output_dir + "results.tex " + Settings::outputDir + "latexCompose.xsl "
	//				+ settings_benchmarks().output_file_xml).c_str());
	//	fs::remove(fs::path(settings_benchmarks().output_dir + "latexCompose.xsl"));
	//}

	if (settings_benchmarks().output_dir != "") {
		std::filesystem::path oloc = std::filesystem::path(settings_benchmarks().output_dir);
		if(!std::filesystem::exists(oloc) ||!std::filesystem::is_directory(oloc))
		{
			BENCHMAX_LOG_FATAL("benchmax", "Output directory does not exist: " << oloc);
			exit(0);
		}
	}

	return true;
}

void loadTools(Tools& tools) {
	createTools<Tool>(settings_tools().tools_generic, tools);
	createTools<SMTRAT>(settings_tools().tools_smtrat, tools);
	createTools<SMTRAT_OPB>(settings_tools().tools_smtrat_opb, tools);
	createTools<Minisatp>(settings_tools().tools_minisatp, tools);
	createTools<Z3>(settings_tools().tools_z3, tools);
}
void loadBenchmarks(std::vector<BenchmarkSet>& benchmarks) {
	for (const auto& p: settings_benchmarks().input_directories) {
		std::filesystem::path path(p);
		if (std::filesystem::exists(path)) {
			BENCHMAX_LOG_INFO("benchmax.benchmarks", "Adding benchmark " << path.native());
			benchmarks.emplace_back(path);
		} else {
			BENCHMAX_LOG_WARN("benchmax", "Benchmark path " << p << " does not exist.");
		}
	}
}

/**
 *
 * @param _signal
 */
void handleSignal(int)
{
	BENCHMAX_LOG_WARN("benchmax", "User abort!");
	exit(-1);
}

/**
 * Main program.
 */
int main(int argc, char** argv)
{
	std::signal(SIGINT, &handleSignal);
	
	// init benchmax
	if (!initApplication(argc, argv)) {
		return 0;
	}
	
	Tools tools;
	loadTools(tools);
	std::vector<BenchmarkSet> benchmarks;
	loadBenchmarks(benchmarks);

	if(benchmarks.empty()) {
		BENCHMAX_LOG_ERROR("benchmax", "No benchmarks were found. Specify a valid location with --directory.");
		return 0;
	}
	benchmax::run_backend(settings_operation().backend, tools, benchmarks);

	return 0;
}
