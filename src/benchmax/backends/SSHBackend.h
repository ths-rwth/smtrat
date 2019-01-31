/**
 * @file SSHBackend.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <future>
#include <queue>

#include <regex>
using std::regex;
using std::regex_match;

#include "../ssh/SSHSettings.h"
#include "../ssh/SSHScheduler.h"

namespace benchmax {
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
	virtual void execute(const Tool* tool, const fs::path& file, const fs::path& baseDir) {
		// Make sure enough jobs are active.
		while (scheduler->runningJobs() > scheduler->workerCount() * 2) {
			if (jobs.front().wait_for(std::chrono::milliseconds(1)) == std::future_status::ready) {
				waitAndPop();
			}
		}
		BENCHMAX_LOG_DEBUG("benchmax.backend", "Starting job.");
		jobs.push(std::async(std::launch::async, &ssh::SSHScheduler::executeJob, scheduler, tool, file, baseDir, this));
	}
public:
	SSHBackend(): Backend() {
		scheduler = new ssh::SSHScheduler();
	}
	~SSHBackend() {
		while (!jobs.empty()) waitAndPop();
	}
};

}
