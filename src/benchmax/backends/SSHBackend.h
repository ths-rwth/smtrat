/**
 * @file SSHBackend.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <future>
#include <thread>

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

//#define USE_STD_ASYNC

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
#ifdef USE_STD_ASYNC
	std::queue<std::future<bool>> jobs;
#else
	std::queue<std::thread> jobs;
#endif
	ssh::SSHScheduler* scheduler;
	
protected:
	virtual void startTool(const Tool& tool) {
		scheduler->uploadTool(tool);
	}
	virtual void execute(const Tool& tool, const fs::path& file) {
		//BENCHMAX_LOG_WARN("benchmax", "Executing...");
#if 1
#ifdef USE_STD_ASYNC
		jobs.push(std::async(std::launch::async, &ssh::SSHScheduler::executeJob, scheduler, tool, file, std::ref(mResults)));
#else
		jobs.push(std::thread(&ssh::SSHScheduler::executeJob, scheduler, tool, file, std::ref(mResults)));
#endif
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
#ifdef USE_STD_ASYNC
			jobs.front().wait();
#else
			jobs.front().join();
#endif
			jobs.pop();
		}
	}
};

}
