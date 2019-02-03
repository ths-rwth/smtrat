#include "SSHScheduler.h"

#ifdef BENCHMAX_SSH

#include <atomic>
#include <chrono>
#include <functional>
#include <regex>
#include <string>
#include <sys/stat.h>
#include <thread>

#include <libssh/callbacks.h>

#include "Node.h"
#include "SSHConnection.h"
#include "SSHSettings.h"
#include <benchmax/logging.h>

namespace benchmax {
namespace ssh {

/**
 * Parses a node identifier of the format `server[:port]@[numberOfCores]@user@password`
 * @param _nodeAsString
 * @return 
 */
Node getNode(const std::string& _nodeAsString)
{
	std::regex noderegex("([^:@]+)(?::([^@]+))?@([^:@]+)(?::(\\d+))?(?:@(\\d+))?(?:#(\\d+))?");
	std::smatch matches;
	if (std::regex_match(_nodeAsString, matches, noderegex)) {
		std::string username = matches[1];
		std::string password = matches[2];
		std::string hostname = matches[3];
		unsigned long port = 22;
		unsigned long cores = 1;
		std::size_t connections = 1;
		try {
			if (matches[4] != "") port = std::stoul(matches[4]);
			if (matches[5] != "") cores = std::stoul(matches[5]);
			if (matches[6] != "") connections = std::stoul(matches[6]);
		} catch (std::out_of_range) {
			BENCHMAX_LOG_ERROR("benchmax", "Value for port or number of cores is out of range.");
			BENCHMAX_LOG_ERROR("benchmax", "\tPort: " << matches[4]);
			BENCHMAX_LOG_ERROR("benchmax", "\tCores: " << matches[5]);
		}
		return {hostname, username, password, (unsigned short)port, cores, connections};
	} else {
		BENCHMAX_LOG_ERROR("benchmax", "Invalid format for node specification. Use the following format:");
		BENCHMAX_LOG_ERROR("benchmax", "\t<user>[:<password>]@<hostname>[:<port = 22>][@<cores = 1>][#<connections = 1>]");
		exit(1);
	}
}

SSHConnection* SSHScheduler::get() {
	std::lock_guard<std::mutex> lock(mMutex);
	while (true) {
		for (auto& c: mConnections) {
			if (c->jobFree()) {
				c->newJob();
				return c;
			}
		}
		std::this_thread::yield();
		std::this_thread::sleep_for(std::chrono::milliseconds(100));
	}
}
std::string SSHScheduler::tmpDirName(const Tool* tool, const fs::path& file) const {
	return "benchmax-" + std::to_string(settings_core().start_time) + "-" + std::to_string(std::size_t(tool)) + "-" + std::to_string(std::hash<std::string>()(file.native()));
}
SSHScheduler::SSHScheduler(): mWorkerCount(0), mRunningJobs(0) {
	ssh_threads_set_callbacks(ssh_threads_get_pthread());
	ssh_init();
	for (const auto& s: settings_ssh().nodes) {
		Node n = getNode(s);
		for (std::size_t i = 0; i < n.connections; i++) {
			mConnections.push_back(new SSHConnection(n));
		}
		mWorkerCount += n.connections * n.cores;
	}
}
SSHScheduler::~SSHScheduler() {
	for (auto& c: mConnections) delete c;
}

void SSHScheduler::uploadTool(const Tool* tool) {
	std::lock_guard<std::mutex> lock(mMutex);
	BENCHMAX_LOG_DEBUG("benchmax.ssh", "Uploading " << tool);
	std::set<std::string> nodes;
	for (SSHConnection* c: mConnections) {
		// Check if we have already uploaded to this host
		if (!nodes.insert(c->getNode().hostname).second) continue;
		while (!c->jobFree()) {
			std::this_thread::sleep_for(std::chrono::milliseconds(10));
		}
		c->uploadFile(tool->binary().native(), settings_ssh().basedir, tool->binary().filename().native(), S_IRWXU);
	}
}

bool SSHScheduler::executeJob(const Tool* tool, const fs::path& file, const fs::path& baseDir, Backend* backend) {
	mRunningJobs++;
	SSHConnection* c = get();
	BENCHMAX_LOG_INFO("benchmax.ssh", "Executing " << removePrefix(file.native(), settings_benchmarks().input_directories_common_prefix));
	// Create temporary directory
	std::string folder = c->createTmpDir(tmpDirName(tool,file));
	// Upload benchmark file
	c->uploadFile(file, folder, file.filename().native());
	// Execute benchmark run
	BenchmarkResult result;
	std::string cmdLine = tool->getCommandline(folder + file.filename().native(), settings_ssh().basedir + tool->binary().filename().native());
	if (!c->executeCommand(cmdLine, result)) {
		BENCHMAX_LOG_ERROR("benchmax.ssh", "Failed to execute command.");
	}
	// Remove temporary directory
	c->removeDir(folder);
	// Store result
	backend->addResult(tool, file, baseDir, result);
	c->finishJob();
	mRunningJobs--;
	return true;
}

}
}

#endif