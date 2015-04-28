#pragma once

#include <chrono>
#include <functional>
#include <string>
#include <sys/stat.h>
#include <thread>

#include "Node.h"
#include "SSHConnection.h"
#include "../Settings.h"
#include "../logging.h"
#include "../BenchmarkStatus.h"

namespace benchmax {
namespace ssh {

	
/**
 * Parses a node identifier of the format `server[:port]@[numberOfCores]@user@password`
 * @param _nodeAsString
 * @return 
 */
Node getNode(const string& _nodeAsString)
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
		return {hostname, username, password, (unsigned short)port, cores};
	} else {
		BENCHMAX_LOG_ERROR("benchmax", "Invalid format for node specification. Use the following format:");
		BENCHMAX_LOG_ERROR("benchmax", "\t<user>:<password>@<hostname>[:<port = 22>][@<cores = 1>]");
		exit(1);
	}
}

class SSHScheduler {
private:
	std::vector<SSHConnection*> connections;
	std::mutex mutex;
	
	SSHConnection* get() {
		std::lock_guard<std::mutex> lock(mutex);
		while (true) {
			for (auto& c: connections) {
				if (!c->busy()) return c;
			}
			std::this_thread::sleep_for(std::chrono::milliseconds(100));
		}
	}
	std::string tmpDirName(const fs::path& file) const {
		return "benchmax-" + std::to_string(Settings::startTime) + "-" + std::to_string(std::hash<std::string>()(file.native()));
	}
public:
	SSHScheduler() {
		for (const auto& s: Settings::ssh_nodes) {
			connections.push_back(new SSHConnection(getNode(s)));
		}
	}
	~SSHScheduler() {
		for (auto& c: connections) delete c;
	}
	
	void uploadTool(const Tool& tool) {
		BENCHMAX_LOG_WARN("benchmax.ssh", "Uploading " << tool);
		std::set<std::string> nodes;
		for (SSHConnection* c: connections) {
			// Check if we have already uploaded to this host
			if (!nodes.insert(c->getNode().hostname).second) continue;
			c->uploadFile(tool.binary().native(), Settings::ssh_basedir, tool.binary().filename().native(), S_IRWXU);
		}
	}
	
	bool executeJob(const Tool& tool, const fs::path& file) {
		BENCHMAX_LOG_WARN("benchmax.ssh", "Executing " << file);
		SSHConnection* c = get();
		// Create temporary directory
		std::string folder = c->createTmpDir(tmpDirName(file));
		// Upload benchmark file
		c->uploadFile(file, folder, file.filename().native());
		BenchmarkResults result;
		std::string cmdLine = tool.getCommandline(folder + file.filename().native(), Settings::ssh_basedir + tool.binary().filename().native());
		if (c->executeCommand(cmdLine, result)) {
			std::cout << result << std::endl;
		} else {
			std::cout << "Failed to execute command." << std::endl;
		}
		c->removeDir(folder);
		return true;
	}
};

}
}
