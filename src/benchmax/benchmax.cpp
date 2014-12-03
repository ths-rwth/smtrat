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
#include "Benchmark.h"
#include "Tool.h"
#include "Node.h"
#include "Settings.h"

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

const string COPYRIGHT =
	"Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Sebastian Junges, Erika Abraham\r\nThis program comes with ABSOLUTELY NO WARRANTY.\r\nThis is free software, and you are welcome to redistribute it \r\nunder certain conditions; use the command line argument --disclaimer in order to get the conditions and warranty disclaimer.";
const string WARRANTY =
	"THERE IS NO WARRANTY FOR THE PROGRAM, TO THE EXTENT PERMITTED BY APPLICABLE LAW. EXCEPT WHEN OTHERWISE STATED IN WRITING THE COPYRIGHT HOLDERS AND/OR OTHER PARTIES PROVIDE THE PROGRAM “AS IS” WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESSED OR IMPLIED, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE. THE ENTIRE RISK AS TO THE QUALITY AND PERFORMANCE OF THE PROGRAM IS WITH YOU. SHOULD THE PROGRAM PROVE DEFECTIVE, YOU ASSUME THE COST OF ALL NECESSARY SERVICING, REPAIR OR CORRECTION.";
const unsigned NUMBER_OF_EXAMPLES_TO_SOLVE = 6;

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

void addToTools(const std::vector<std::string>& pathes, benchmax::ToolInterface interface, std::vector<Tool*>& tools)
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
				tools.back()->addArgument(matches[i]);
			}
		}
	}
}

/**
 * Parses a node identifier of the format `server[:port]@[numberOfCores]@user@password`
 * @param _nodeAsString
 * @return 
 */
benchmax::Node* getNode(const string& _nodeAsString)
{
	regex noderegex("([^:]+):([^@]+)@([^:@]+)(?::(\\d+))?(?:@(\\d+))?");
	std::smatch matches;
	if (regex_match(_nodeAsString, matches, noderegex)) {
		std::string username = matches[1];
		std::string password = matches[2];
		std::string hostname = matches[3];
		unsigned long port = 22;
		unsigned long cores = 1;
		try {
			if (matches[4] != "") port = std::stoul(matches[4]);
			if (matches[5] != "") cores = std::stoul(matches[5]);
		} catch (std::out_of_range) {
			BENCHMAX_LOG_ERROR("benchmax", "Value for port or number of cores is out of range.");
			BENCHMAX_LOG_ERROR("benchmax", "\tPort: " << matches[4]);
			BENCHMAX_LOG_ERROR("benchmax", "\tCores: " << matches[5]);
		}
		return new benchmax::Node(hostname, username, password, (unsigned short)cores, (unsigned short)port);
	} else {
		BENCHMAX_LOG_ERROR("benchmax", "Invalid format for node specification. Use the following format:");
		BENCHMAX_LOG_ERROR("benchmax", "\t<user>:<password>@<hostname>[:<port = 22>][@<cores = 1>]");
		return nullptr;
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

bool initApplication(const benchmax::Settings& s, std::vector<benchmax::Benchmark*>& _benchmarks, Stats*& _stats, std::vector<Tool*>& _tools)
{

	// add the remote nodes
	for (const auto& node: Settings::nodes) {
		Settings::Nodes.push_back(getNode(node));
	}

	if(s.has("help")) {
		std::cout << s;
		return false;
	}
	if(s.has("disclaimer")) {
		printDisclaimer();
		return false;
	}
	carl::logging::logger().filter("stdout")
		("benchmax", carl::logging::LogLevel::LVL_DEBUG)
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
					   (!Settings::Nodes.empty() ? Stats::STATS_COLLECTION : Stats::BENCHMARK_RESULT));
	if(Settings::Nodes.empty())
	{
		for (const auto& tool: _tools) {
			_stats->addSolver(fs::path(tool->path()).filename().generic_string());
		}
	}

	// For each path, and each tool, we add a benchmark to be computed.
	for (const auto& p: s.pathes) {
		fs::path path(p);
		if (fs::exists(path)) {
			for (const auto& tool: _tools) {
				_benchmarks.push_back(
				new benchmax::Benchmark(path.generic_string(), tool, Settings::ValidationTool, s.timeLimit, s.memoryLimit, s.verbose, s.quiet, s.mute,
							  Settings::ProduceLatex, _stats));
			}
		} else {
			BENCHMAX_LOG_WARN("benchmax", "Benchmark path " << p << " does not exist.");
		}
	}
	return true;
}

/**
 *
 * @param _signal
 */
void handleSignal(int)
{
	BENCHMAX_LOG_WARN("benchmax", "User abort!");
	while(!Settings::Nodes.empty())
	{
		benchmax::Node* toDelete = Settings::Nodes.back();
		toDelete->cancel();
		Settings::Nodes.pop_back();
		delete toDelete;
	}
	exit(-1);
}

/**
 * Main program.
 */
int main(int argc, char** argv)
{
	benchmax::Settings s(argc, argv);
	Settings::PathOfBenchmarkTool = fs::system_complete(fs::path(argv[0])).native();
	if (Settings::validationtoolpath != "") {
		Settings::ValidationTool = createTool(benchmax::TI_Z3, Settings::validationtoolpath);
	}

	// init benchmarks
	std::vector<benchmax::Benchmark*> benchmarks;
	Stats* stats = NULL;
	std::vector<Tool*> tools;
	if (!initApplication(s, benchmarks, stats, tools)) {
		return 0;
	}

	std::signal(SIGINT, &handleSignal);

	if(benchmarks.empty()) {
		BENCHMAX_LOG_FATAL("benchmax", "No benchmarks were found.");
		return 0;
	}
	
	// run benchmarks
	std::map<std::pair<std::string, std::string>, benchmax::Benchmark*> table;	// table mapping <benchmark,solver> -> result
	std::set<std::string> benchmarkSet, solverSet;

	if(!Settings::Nodes.empty()) {
		// libssh is needed.
		int rc = libssh2_init(0);
		if (rc != 0) {
			BENCHMAX_LOG_FATAL("benchmax", "Failed to initialize libssh2 (return code " << rc << ")");
			exit(1);
		}
	}

	/*
	 * Main loop.
	 */
	if(Settings::Nodes.empty())
	{
		for (const auto& benchmark: benchmarks)
		{
			benchmark->printSettings();
			benchmark->run();
			BENCHMAX_LOG_DEBUG("benchmax", "Benchmark " << benchmark->benchmarkName() << " done!");
			benchmark->printResults();
			if(benchmark->produceLaTeX())
			{
				string benchmarkString = benchmark->benchmarkName() + " (" + boost::lexical_cast<string>(benchmark->benchmarkCount()) + ")";
				table[pair<string, string>(benchmarkString, benchmark->solverName())] = benchmark;
				benchmarkSet.insert(benchmarkString);
				solverSet.insert(benchmark->solverName());
			}
		}

		if(Settings::ValidationTool != nullptr)
		{
			std::string wrongResultPath = Settings::WrongResultPath.substr(0, Settings::WrongResultPath.size() - 1);
			fs::path path(wrongResultPath);
			if(fs::exists(path))
			{
				std::string tarCall = std::string("tar zcfP " + wrongResultPath + ".tgz " + wrongResultPath);
				system(tarCall.c_str());
				fs::remove_all(fs::path(Settings::WrongResultPath));
			}
		}
	}
	else
	{
		int						  nrOfCalls		= 0;
		std::vector<benchmax::Benchmark*>::iterator currentBenchmark = benchmarks.begin();
		std::vector<benchmax::Node*>::iterator	  currentNode	  = Settings::Nodes.begin();
		if(currentBenchmark != benchmarks.end())
			(*currentBenchmark)->printSettings();
		while(currentBenchmark != benchmarks.end())
		{
			if((*currentBenchmark)->done())
			{
				++currentBenchmark;
				if(currentBenchmark == benchmarks.end())
					break;
				(*currentBenchmark)->printSettings();
			}
			if(currentNode == Settings::Nodes.end())
				currentNode = Settings::Nodes.begin();
			if(!(*currentNode)->connected())
			{
				(*currentNode)->createSSHconnection();
			}

			(*currentNode)->updateResponses();

			if((*currentNode)->freeCores() > 0)
			{
				stringstream tmpStream;
				tmpStream << ++nrOfCalls;
				(*currentNode)->assignAndExecuteBenchmarks(**currentBenchmark, NUMBER_OF_EXAMPLES_TO_SOLVE, tmpStream.str());
			}
			++currentNode;
			usleep(100000);	// 100 milliseconds (0.1 seconds);
		}

		unsigned waitedTime = 0;
		//		unsigned numberOfTries = 0;
		// Wait until all nodes have finished.
		BENCHMAX_LOG_INFO("benchmax", "All scheduled!");
		bool allNodesEntirelyIdle = false;
		BENCHMAX_LOG_INFO("benchmax", "Waiting for calls...");
		while(!allNodesEntirelyIdle)
		{
			allNodesEntirelyIdle = true;
			std::vector<benchmax::Node*>::iterator currentNode = Settings::Nodes.begin();
			while(currentNode != Settings::Nodes.end())
			{
				(*currentNode)->updateResponses();
				if(!(*currentNode)->idle())
				{
					allNodesEntirelyIdle = false;
					if(waitedTime > (s.timeLimit * NUMBER_OF_EXAMPLES_TO_SOLVE))
					{
						BENCHMAX_LOG_INFO("benchmax", "Waiting for call...");
						(*currentNode)->sshConnection().logActiveRemoteCalls();
						waitedTime = 0;
					}
					break;
				}
				++currentNode;
			}
			sleep(1);
			++waitedTime;
		}

		// Download files.
		for(std::vector<benchmax::Node*>::const_iterator currentNode = Settings::Nodes.begin(); currentNode != Settings::Nodes.end(); ++currentNode)
		{
			for(std::vector<std::string>::const_iterator jobId = (*currentNode)->jobIds().begin(); jobId != (*currentNode)->jobIds().end(); ++jobId)
			{
				std::stringstream out;
				out << *jobId;
				(*currentNode)->downloadFile(
				Settings::RemoteOutputDirectory + "stats_" + *jobId + ".xml", Settings::outputDir + "stats_" + *jobId + ".xml");
				if(Settings::ValidationTool != nullptr)
				{
					fs::path newloc = fs::path(Settings::WrongResultPath);
					if(!fs::is_directory(newloc))
					{
						fs::create_directories(newloc);
					}
					(*currentNode)->downloadFile(
					Settings::RemoteOutputDirectory + "wrong_results_" + *jobId + ".tgz",
					Settings::WrongResultPath + "wrong_results_" + *jobId + ".tgz");
				}
				fs::path newloc = fs::path(Settings::outputDir + "benchmark_output/");
				if(!fs::is_directory(newloc))
				{
					fs::create_directories(newloc);
				}
				(*currentNode)->downloadFile(
				Settings::RemoteOutputDirectory + "benchmark_" + *jobId + ".out",
				Settings::outputDir + "benchmark_output/benchmark_" + *jobId + ".out");
				stats->addStat("stats_" + *jobId + ".xml");

			}
		}
	}

	if(!Settings::Nodes.empty())
	{
		stats->createStatsCompose(Settings::outputDir + "statsCompose.xsl");
		delete stats;
		Stats::callComposeProcessor();
	}
	else
	{
		delete stats;
	}

	// Delete everything and finish.
	while(!benchmarks.empty())
	{
		benchmax::Benchmark* toDelete = benchmarks.back();
		benchmarks.pop_back();
		delete toDelete;
	}
	while(!tools.empty())
	{
		Tool* toDelete = tools.back();
		tools.pop_back();
		delete toDelete;
	}
	while(!Settings::Nodes.empty())
	{
		benchmax::Node* toDelete = Settings::Nodes.back();
		Settings::Nodes.pop_back();
		delete toDelete;
	}

	// Necessary output message (DO NOT REMOVE IT)
	std::cout << Settings::ExitMessage << std::endl;
	if(!Settings::Nodes.empty())
	{
		libssh2_exit();
	}
	return 0;
}
