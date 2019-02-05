#pragma once

#include <benchmax/config.h>

#ifdef BENCHMAX_SSH

#include <benchmax/backends/Backend.h>
#include <benchmax/logging.h>

#include <atomic>

namespace benchmax {
namespace ssh {

class SSHConnection;

/// Helper class that schedules jobs among a list of SSH connections.
class SSHScheduler {
private:
	/// List of active connections.
	std::vector<std::unique_ptr<SSHConnection>> mConnections;
	/// Mutex.
	std::mutex mMutex;
	/// Number of current workers.
	std::size_t mWorkerCount = 0;
	/// Numbers of running jobs.
	std::atomic<unsigned> mRunningJobs;
	
	/// Return a connection that is not busy.
	const std::unique_ptr<SSHConnection>& get();
	/// Create a name for a temporary directory.
	std::string tmpDirName(const Tool* tool, const fs::path& file) const;
public:
	/// Initializes all SSH connections.
	SSHScheduler();
	
	/// Number of workers.
	std::size_t workerCount() const {
		return mWorkerCount;
	}
	/// Number of running jobs.
	std::size_t runningJobs() const {
		return mRunningJobs;
	}
	/// Upload a tool to all remotes.
	void uploadTool(const Tool* tool);
	/// Execute a single job.
	bool executeJob(const Tool* tool, const fs::path& file, const fs::path& baseDir, Backend* backend);
};

}
}

#endif