/**
 * @file SSHBackend.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <future>
#include <queue>

#ifdef USE_BOOST_REGEX
#include "../../cli/config.h"
#ifdef __VS
#pragma warning(push, 0)
#include <boost/regex.hpp>
#pragma warning(pop)
#else
#include <boost/regex.hpp>
#endif
using boost::regex;
using boost::regex_match;
#else
#include <regex>
using std::regex;
using std::regex_match;
#endif

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
	virtual void execute(const Tool* tool, const fs::path& file) {
		// Make sure enough jobs are active.
		while (scheduler->runningJobs() > scheduler->workerCount() * 2) {
			if (jobs.front().wait_for(std::chrono::milliseconds(5)) == std::future_status::ready) {
				waitAndPop();
			}
		}
		BENCHMAX_LOG_DEBUG("benchmax.backend", "Starting job.");
		jobs.push(std::async(std::launch::async, &ssh::SSHScheduler::executeJob, scheduler, tool, file, std::ref(mResults)));
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
