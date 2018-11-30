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
namespace fs = std::filesystem;

#include <csignal>

#include "logging.h"
#include "BenchmarkSet.h"
#include "tools/Tools.h"
#include "Settings.h"
#include "Stats.h"

#include "backends/CondorBackend.h"
#include "backends/LocalBackend.h"
#include "backends/SSHBackend.h"

#include "utils/regex.h"

using benchmax::Tool;
using benchmax::Stats;
using benchmax::Settings;

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
	
	benchmax::Settings s(argc, argv);
	Settings::PathOfBenchmarkTool = fs::canonical(fs::path(argv[0])).native();

	if(s.has("help")) {
		std::cout << s;
		return false;
	}
	if (s.has("verbose")) {
		carl::logging::logger().filter("stdout")
			("benchmax", carl::logging::LogLevel::LVL_INFO)
			("benchmax.backend", carl::logging::LogLevel::LVL_INFO)
			("benchmax.benchmarks", carl::logging::LogLevel::LVL_DEBUG)
		;
	}
	if(s.has("disclaimer")) {
		std::cout << WARRANTY << std::endl;
		return false;
	}
	if(s.has("compose")) {
		Stats::composeStats(s.composeFiles);
		return false;
	}
	else if(Settings::ProduceLatex)
	{
		Stats::createStatsCompose(Settings::outputDir + "latexCompose.xsl");
		system(
		std::string("xsltproc -o " + Settings::outputDir + "results.tex " + Settings::outputDir + "latexCompose.xsl "
					+ Settings::StatsXMLFile).c_str());
		fs::remove(fs::path(Settings::outputDir + "latexCompose.xsl"));
	}
	
	if (s.has("convert")) {
		BENCHMAX_LOG_INFO("benchmax", "Converting " << s.as<std::string>("convert") << " to ods using import filer " << s.as<std::string>("convert-filter"));
		std::stringstream ss;
		ss << "libreoffice --headless --infilter=" << s.as<std::string>("convert-filter") << " --convert-to ods " << s.as<std::string>("convert");
		system(ss.str().c_str());
		return false;
	}

	if(Settings::outputDir != "")
	{
		fs::path oloc = fs::path(Settings::outputDir);
		if(!fs::exists(oloc) ||!fs::is_directory(oloc))
		{
			BENCHMAX_LOG_FATAL("benchmax", "Output directory does not exist: " << oloc);
			exit(0);
		}
	}

	return true;
}

void loadTools(std::vector<benchmax::Tool*>& tools) {
	benchmax::createTools<benchmax::Tool>(Settings::tools_generic, tools);
	benchmax::createTools<benchmax::SMTRAT>(Settings::tools_smtrat, tools);
	benchmax::createTools<benchmax::SMTRAT_OPB>(Settings::tools_smtrat_opb, tools);
	benchmax::createTools<benchmax::Minisatp>(Settings::tools_minisatp, tools);
	benchmax::createTools<benchmax::Z3>(Settings::tools_z3, tools);
}
void loadBenchmarks(std::vector<benchmax::BenchmarkSet>& benchmarks) {
	for (const auto& p: Settings::pathes) {
		fs::path path(p);
		if (fs::exists(path)) {
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
	
	// init benchmark
	if (!initApplication(argc, argv)) {
		return 0;
	}
	
	std::vector<Tool*> tools;
	loadTools(tools);
	std::vector<benchmax::BenchmarkSet> benchmarks;
	loadBenchmarks(benchmarks);

	if(benchmarks.empty()) {
		BENCHMAX_LOG_FATAL("benchmax", "No benchmarks were found.");
		return 0;
	}
	if (Settings::backend == "condor") {
		BENCHMAX_LOG_INFO("benchmax", "Using condor backend.");
		benchmax::CondorBackend backend;
		backend.run(tools, benchmarks);
	} else if (Settings::backend == "local") {
		BENCHMAX_LOG_INFO("benchmax", "Using local backend.");
		benchmax::LocalBackend backend;
		backend.run(tools, benchmarks);
	} else if (Settings::backend == "ssh") {
		BENCHMAX_LOG_INFO("benchmax", "Using ssh backend.");
		// libssh is needed.
		benchmax::SSHBackend backend;
		backend.run(tools, benchmarks);
	} else {
		BENCHMAX_LOG_ERROR("benchmax", "Invalid backend \"" << Settings::backend << "\".");
	}
	
	for (auto& tp: tools) delete tp;

	return 0;
}
