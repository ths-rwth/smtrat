/**
 * @file SSHBackend.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include "Backend.h"
#include "ssh/SSHSettings.h"
#include <benchmax/config.h>

#ifdef BENCHMAX_SSH

#include "ssh/SSHScheduler.h"

#include <future>
#include <queue>

namespace benchmax {
/**
 * Backend using remote computation nodes via SSH.
 * This backend connects to one or more remote computations nodes via SSH and runs all benchmarks concurrently.
 * The queueing is performed manually by the SSHScheduler class.
 * 
 * Additionally to simply connecting multiple times, SSH also allows for multiplexing within a single connection.
 * As SSH limits both the number of concurrent connections and the number of channels within a single connection, we combine both mechanisms.
 * The number of concurrent connections is specified by `connections` while the number of channels is specified by `cores` of a Node.
 */
class SSHBackend: public Backend {
private:
	std::queue<std::future<bool>> jobs;

	void waitAndPop() {
		jobs.front().wait();
		jobs.pop();
		madeProgress();
	}
	ssh::SSHScheduler* scheduler;
	
protected:
	virtual void startTool(const Tool* tool) {
		scheduler->uploadTool(tool);
	}
	virtual void finalize() {
		while (!jobs.empty()) waitAndPop();
	}
	virtual void execute(const Tool* tool, const fs::path& file) {
		// Make sure enough jobs are active.
		while (scheduler->runningJobs() > scheduler->workerCount() * 2) {
			if (jobs.front().wait_for(std::chrono::milliseconds(1)) == std::future_status::ready) {
				waitAndPop();
			}
		}
		BENCHMAX_LOG_DEBUG("benchmax.backend", "Starting job.");
		jobs.push(std::async(std::launch::async, &ssh::SSHScheduler::executeJob, scheduler, tool, file, this));
	}
public:
	SSHBackend(): Backend() {
		scheduler = new ssh::SSHScheduler();
	}
};

}

#else

namespace benchmax {
class SSHBackend: public Backend {
public:
	SSHBackend(): Backend() {}
	~SSHBackend() {}
	/// Dummy if SSH is disabled.
	void run(const Jobs&, bool wait_for_termination) {
		BENCHMAX_LOG_ERROR("benchmax", "This version of benchmax was compiled without support for SSH.");
	}
};

}

#endif