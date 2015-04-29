/**
 * @file SSHBackend.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <future>

#ifdef USE_BOOST_REGEX
#include <boost/regex.hpp>
using boost::regex;
using boost::regex_match;
#else
#include <regex>
using std::regex;
using std::regex_match;
#endif

#include "BackendData.h"
#include "../ssh/Node.h"
#include "../newssh/SSHScheduler.h"

namespace benchmax {

/**
 * Parses a node identifier of the format `server[:port]@[numberOfCores]@user@password`
 * @param _nodeAsString
 * @return 
 */
benchmax::Node getNode(const string& _nodeAsString)
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
		return benchmax::Node(hostname, username, password, (unsigned short)cores, (unsigned short)port);
	} else {
		BENCHMAX_LOG_ERROR("benchmax", "Invalid format for node specification. Use the following format:");
		BENCHMAX_LOG_ERROR("benchmax", "\t<user>:<password>@<hostname>[:<port = 22>][@<cores = 1>]");
		exit(1);
	}
}

class SSHBackend: public Backend {
private:
	std::queue<std::future<bool>> jobs;
	ssh::SSHScheduler* scheduler;
	
protected:
	virtual void startTool(const Tool& tool) {
		scheduler->uploadTool(tool);
	}
	virtual void execute(const Tool& tool, const fs::path& file) {
		BENCHMAX_LOG_WARN("benchmax", "Executing...");
#if 0
		jobs.push(std::async(std::launch::async, &ssh::SSHScheduler::executeJob, scheduler, tool, file, mResults));
#else
		scheduler->executeJob(tool, file, mResults);
#endif
	}
public:
	SSHBackend(): Backend() {
		scheduler = new ssh::SSHScheduler();
	}
	~SSHBackend() {
		while (!jobs.empty()) {
			jobs.front().wait();
			jobs.pop();
		}
	}
};

class OldSSHBackend: public Backend {
	std::vector<benchmax::Node> nodes;
	const unsigned NUMBER_OF_EXAMPLES_TO_SOLVE = 6;
public:
	OldSSHBackend(): Backend() {
		int rc = libssh2_init(0);
		if (rc != 0) {
			BENCHMAX_LOG_FATAL("benchmax", "Failed to initialize libssh2 (return code " << rc << ")");
			exit(1);
		}
		
		// add the remote nodes
		for (const auto& node: Settings::ssh_nodes) {
			nodes.push_back(getNode(node));
		}
	}
	~OldSSHBackend() {
		libssh2_exit();
	}
	void run(const std::vector<Tool*>&, const std::vector<BenchmarkSet>& benchmarks) {
		int nrOfCalls = 0;
		auto currentBenchmark = benchmarks.begin();
		std::vector<benchmax::Node>::iterator currentNode = nodes.begin();
		if(currentBenchmark != benchmarks.end())
			currentBenchmark->printSettings();
		while(currentBenchmark != benchmarks.end())
		{
			if(currentBenchmark->done())
			{
				++currentBenchmark;
				if(currentBenchmark == benchmarks.end())
					break;
				currentBenchmark->printSettings();
			}
			if(currentNode == nodes.end())
				currentNode = nodes.begin();
			if(!(*currentNode).connected())
			{
				(*currentNode).createSSHconnection();
			}

			(*currentNode).updateResponses();

			if((*currentNode).freeCores() > 0)
			{
				stringstream tmpStream;
				tmpStream << ++nrOfCalls;
				//(*currentNode).assignAndExecuteBenchmarks(*currentBenchmark, NUMBER_OF_EXAMPLES_TO_SOLVE, tmpStream.str());
			}
			++currentNode;
			usleep(100000);	// 100 milliseconds (0.1 seconds);
		}
		waitForJobs();
		downloadFiles();
	}
	void waitForJobs() {
		unsigned waitedTime = 0;
		//		unsigned numberOfTries = 0;
		// Wait until all nodes have finished.
		BENCHMAX_LOG_INFO("benchmax", "All scheduled!");
		bool allNodesEntirelyIdle = false;
		BENCHMAX_LOG_INFO("benchmax", "Waiting for calls...");
		while(!allNodesEntirelyIdle)
		{
			allNodesEntirelyIdle = true;
			std::vector<benchmax::Node>::iterator currentNode = nodes.begin();
			while(currentNode != nodes.end())
			{
				(*currentNode).updateResponses();
				if(!(*currentNode).idle())
				{
					allNodesEntirelyIdle = false;
					if(waitedTime > (Settings::timeLimit * NUMBER_OF_EXAMPLES_TO_SOLVE))
					{
						BENCHMAX_LOG_INFO("benchmax", "Waiting for call...");
						(*currentNode).sshConnection().logActiveRemoteCalls();
						waitedTime = 0;
					}
					break;
				}
				++currentNode;
			}
			sleep(1);
			++waitedTime;
		}
	}
	void downloadFiles() {
		for(std::vector<benchmax::Node>::iterator currentNode = nodes.begin(); currentNode != nodes.end(); ++currentNode)
		{
			for(std::vector<std::string>::const_iterator jobId = (*currentNode).jobIds().begin(); jobId != (*currentNode).jobIds().end(); ++jobId)
			{
				std::stringstream out;
				out << *jobId;
				(*currentNode).downloadFile(
				Settings::RemoteOutputDirectory + "stats_" + *jobId + ".xml", Settings::outputDir + "stats_" + *jobId + ".xml");
				if(Settings::ValidationTool != nullptr)
				{
					fs::path newloc = fs::path(Settings::WrongResultPath);
					if(!fs::is_directory(newloc))
					{
						fs::create_directories(newloc);
					}
					(*currentNode).downloadFile(
					Settings::RemoteOutputDirectory + "wrong_results_" + *jobId + ".tgz",
					Settings::WrongResultPath + "wrong_results_" + *jobId + ".tgz");
				}
				fs::path newloc = fs::path(Settings::outputDir + "benchmark_output/");
				if(!fs::is_directory(newloc))
				{
					fs::create_directories(newloc);
				}
				(*currentNode).downloadFile(
				Settings::RemoteOutputDirectory + "benchmark_" + *jobId + ".out",
				Settings::outputDir + "benchmark_output/benchmark_" + *jobId + ".out");
				//data->stats->addStat("stats_" + *jobId + ".xml");
			}
		}
	}
};

}
