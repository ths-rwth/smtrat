#pragma once

#include <benchmax/config.h>

#ifdef BENCHMAX_SSH

#include <benchmax/backends/Backend.h>
#include <benchmax/BenchmarkStatus.h>
#include <benchmax/logging.h>

#include <atomic>

namespace benchmax {
namespace ssh {

class SSHConnection;

class SSHScheduler {
private:
	std::vector<SSHConnection*> mConnections;
	std::mutex mMutex;
	std::size_t mWorkerCount = 0;
	std::atomic<unsigned> mRunningJobs;
		
	SSHConnection* get();
	std::string tmpDirName(const Tool* tool, const fs::path& file) const;
public:
	SSHScheduler();
	~SSHScheduler();
	
	std::size_t workerCount() const {
		return mWorkerCount;
	}
	std::size_t runningJobs() const {
		return mRunningJobs;
	}
	
	void uploadTool(const Tool* tool);
	
	bool executeJob(const Tool* tool, const fs::path& file, const fs::path& baseDir, Backend* backend);
};

}
}

#endif