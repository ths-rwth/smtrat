/**
 * @file ThreadPool.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <atomic>
#include <cassert>
#include <future>
#include <queue>
#include <sstream>
#include <thread>
#include <tuple>
#include <utility>
#include <vector>

#include "Checker.h"
#include "Node.h"

namespace delta {

class Executor {
private:
	std::queue<std::future<void>> jobs;
	std::mutex tempMutex;
	std::queue<std::string> tempfiles;
	std::atomic<bool> found;
	std::atomic<int> curId;
	std::atomic<unsigned> jobcount;
	std::atomic<unsigned> progress;
	std::mutex resultMutex;
	std::pair<Node, std::string> result;
	std::string tempPrefix;
	
	std::string nextTempfile() {
		std::lock_guard<std::mutex> guard(tempMutex);
		if (tempfiles.empty()) {
			std::stringstream ss;
			ss << tempPrefix << "-" << curId++;
			return ss.str();
		}
		auto r = tempfiles.front();
		tempfiles.pop();
		return r;
	}
	void returnTempfile(const std::string& temp) {
		std::lock_guard<std::mutex> guard(tempMutex);
		tempfiles.push(temp);
	}

	void performCheck(const Node& n, const Checker& c, const std::string& message) {
		progress++;
		if (found) return;
		std::string temp = nextTempfile();
		bool res = c(n, temp);
		returnTempfile(temp);
		if (res && !found) {
			std::lock_guard<std::mutex> guard(resultMutex);
			found = true;
			result = std::make_pair(n, message);
		}
	}
public:
	Executor(const std::string& tempPrefix): found(false), curId(0), tempPrefix(tempPrefix) {
		reset();
	}
	~Executor() {
		reset();
	}
	void check(Node n, const Checker& c, const std::string& message) {
		if (found) return;
		jobcount++;
		jobs.push(std::async(std::launch::async, &Executor::performCheck, this, n, c, message));
	}
	bool wait() {
		while (!jobs.empty() && jobs.front().valid()) jobs.pop();
		if (!jobs.empty()) {
			jobs.front().get();
			jobs.pop();
		}
		return jobs.empty();
	}
	void reset() {
		while (!jobs.empty()) wait();
		found = false;
		result = std::make_pair(Node(), "");
		jobcount = 0;
		progress = 0;
	}
	bool hasResult() {
		return found;
	}
	std::pair<Node, std::string> getResult() {
		assert(hasResult());
		return result;
	}
	std::pair<unsigned, unsigned> getProgress() const {
		return std::make_pair(progress.load(), jobcount.load());
	}
};

}