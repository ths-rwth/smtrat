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
 * @file benchmax.cpp
 *
 * @author Sebastian Junges
 * @author Ulrich Loup
 *
 * @since 2012-02-01
 * @version 2013-04-23
 */

#include <iostream>
#include <boost/filesystem/path.hpp>
#include <signal.h>

#include "logging.h"
#include "BenchmarkSet.h"
#include "Tool.h"
#include "Settings.h"

#include "backends/BackendData.h"
#include "backends/CondorBackend.h"
#include "backends/LocalBackend.h"
#include "backends/SSHBackend.h"

#include "carl/formula/Formula.h"

#ifdef USE_BOOST_REGEX
#include <boost/regex.hpp>
using boost::regex;
using boost::regex_match;
#else
#include <regex>
using std::regex;
using std::regex_match;
#endif

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

void printDisclaimer()
{
	std::cout << WARRANTY << std::endl;
}

void addToTools(const std::vector<std::string>& pathes, benchmax::ToolInterface interface, std::vector<Tool>& tools)
{
	for (const auto& p: pathes) {
		regex r("([^ ]+)(?: ([^ ]+))*");
		std::smatch matches;
		if (regex_match(p, matches, r)) {
			fs::path path(matches[1]);
			fs::file_status status = fs::status(path);
			if (status.type() != fs::file_type::regular_file) {
				BENCHMAX_LOG_WARN("benchmax", "The tool " << path << " does not seem to be a file. We skip it.");
				continue;
			}
			if ((status.permissions() & (fs::others_exe | fs::group_exe | fs::owner_exe)) == 0) {
				BENCHMAX_LOG_WARN("benchmax", "The tool " << path << " does not seem to be executable. We skip it.");
				continue;
			}
			tools.push_back(createTool(interface, matches[1]));
			for (std::size_t i = 2; i < matches.size(); i++) {
				tools.back().addArgument(matches[i]);
			}
		}
	}
}

void checkPathCorrectness(std::string& _path)
{
	if(!_path.empty())
	{
		if(_path.at(_path.size() - 1) != '/')
			_path += "/";
	}
}

bool initApplication(const benchmax::Settings& s, std::vector<benchmax::BenchmarkSet*>& _benchmarks, Stats*& _stats, std::vector<Tool>& _tools)
{


	if(s.has("help")) {
		std::cout << s;
		return false;
	}
	if(s.has("disclaimer")) {
		printDisclaimer();
		return false;
	}
	carl::logging::logger().configure("stdout", std::cout);
	carl::logging::logger().filter("stdout")
		("benchmax", carl::logging::LogLevel::LVL_INFO)
		("benchmax.ssh", carl::logging::LogLevel::LVL_INFO)
	;
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

	if(Settings::outputDir != "")
	{
		fs::path oloc = fs::path(Settings::outputDir);
		if(!fs::exists(oloc) ||!fs::is_directory(oloc))
		{
			BENCHMAX_LOG_FATAL("benchmax", "Output directory does not exist: " << oloc);
			exit(0);
		}
	}

	if (!s.mute) {
		printWelcome();
	}

	// Check the correctness of the given paths and correct them if necessary
	checkPathCorrectness(Settings::WrongResultPath);
	checkPathCorrectness(Settings::outputDir);
	
	// add the different applications to the list of tools, with the appropriate interface.
	addToTools(s.smtratapps, benchmax::TI_SMTRAT, _tools);
	addToTools(s.z3apps, benchmax::TI_Z3, _tools);
	addToTools(s.isatapps, benchmax::TI_ISAT, _tools);
	addToTools(s.redlog_rlqeapps, benchmax::TI_REDLOG_RLQE, _tools);
	addToTools(s.redlog_rlcadapps, benchmax::TI_REDLOG_RLCAD, _tools);
	addToTools(s.qepcadapps, benchmax::TI_QEPCAD, _tools);

	// Collect all used solvers in the statisticsfile.
	_stats = new Stats(Settings::outputDir + Settings::StatsXMLFile,
					   (!Settings::nodes.empty() ? Stats::STATS_COLLECTION : Stats::BENCHMARK_RESULT));
	if (Settings::nodes.empty())
	{
		for (const auto& tool: _tools) {
			_stats->addSolver(fs::path(tool.path()).filename().generic_string());
		}
	}

	// For each path, and each tool, we add a benchmark to be computed.
	for (const auto& p: s.pathes) {
		fs::path path(p);
		if (fs::exists(path)) {
			for (const auto& tool: _tools) {
				_benchmarks.push_back(new benchmax::BenchmarkSet(path.generic_string(), tool, Settings::ProduceLatex, _stats));
			}
		} else {
			BENCHMAX_LOG_WARN("benchmax", "Benchmark path " << p << " does not exist.");
		}
	}
	return true;
}

void loadTools(benchmax::Backend& backend) {
	
}
void loadBenchmarks(benchmax::Backend& backend) {
	for (const auto& p: Settings::pathes) {
		fs::path path(p);
		if (fs::exists(path)) {
			backend.addBenchmark(benchmax::BenchmarkSet(path, Settings::ProduceLatex, _stats))
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
	
	benchmax::Settings s(argc, argv);
	Settings::PathOfBenchmarkTool = fs::system_complete(fs::path(argv[0])).native();

	benchmax::BackendData data;
	
	// init benchmark
	std::vector<Tool> tools;
	if (!initApplication(s, data.benchmarks, data.stats, tools)) {
		return 0;
	}

	if(data.benchmarks.empty()) {
		BENCHMAX_LOG_FATAL("benchmax", "No benchmarks were found.");
		return 0;
	}
	if (Settings::backend == "condor") {
		BENCHMAX_LOG_INFO("benchmax", "Using condor backend.");
		benchmax::CondorBackend backend(&data);
		backend.run();
	} else if (Settings::backend == "local") {
		BENCHMAX_LOG_INFO("benchmax", "Using local backend.");
		benchmax::LocalBackend backend;
		backend.run();
	} else if (Settings::backend == "ssh") {
		BENCHMAX_LOG_INFO("benchmax", "Using ssh backend.");
		// libssh is needed.
		benchmax::SSHBackend backend(&data);
		backend.run();
		
		data.stats->createStatsCompose(Settings::outputDir + "statsCompose.xsl");
		Stats::callComposeProcessor();
		// Necessary output message (DO NOT REMOVE IT)
		std::cout << Settings::ExitMessage << std::endl;
	} else {
		BENCHMAX_LOG_ERROR("benchmax", "Invalid backend \"" << Settings::backend << "\".");
	}

	return 0;
}
