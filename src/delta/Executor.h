/**
 * @file ThreadPool.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <atomic>
#include <cassert>
#include <chrono>
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

/**
 * This class takes care of asynchronous execution of calls to the solver.
 */
class Executor {
private:
	/// List of job results not checked yet.
	std::queue<std::future<void>> jobs;
	/// Prefix for temporary files.
	std::string tempPrefix;
	/// Mutex for changes to tempfiles.
	std::mutex tempMutex;
	/// List of temporary files that are available.
	std::queue<std::string> tempfiles;
	/// Id of next temporary file.
	std::atomic<int> nextTempId;
	/// Flag if a call was successful.
	std::atomic<bool> found;
	/// Number of jobs that have been started.
	std::atomic<unsigned> jobcount;
	/// Number of jobs that have terminated.
	std::atomic<unsigned> progress;
	/// Mutex for changes to result.
	std::mutex resultMutex;
	/// Result of successful call, consisting of node and message.
	std::pair<Node, std::string> result;
	/// Number of actual calls to the solver.
	std::atomic<unsigned> callCount;
	
	/**
	 * Retrieve a filename for a temporary file that is not in use.
     * @return Temporary filename.
     */
	std::string nextTempfile() {
		std::lock_guard<std::mutex> guard(tempMutex);
		if (tempfiles.empty()) {
			std::stringstream ss;
			ss << tempPrefix << "-" << nextTempId++;
			return ss.str();
		}
		auto r = tempfiles.front();
		tempfiles.pop();
		return r;
	}
	/**
	 * Returns a filename to the pool of available filenames.
     * @param temp Temporary filename.
     */
	void returnTempfile(const std::string& temp) {
		std::lock_guard<std::mutex> guard(tempMutex);
		tempfiles.push(temp);
	}

	/**
	 * Calls the checker and checks the result.
	 * Method that is called by `std::async`.
     * @param n Node to check.
     * @param checker Checker.
     * @param message Message, if check is successful.
     */
	void performCheck(const Node& n, const Checker& checker, const std::string& message) {
		progress++;
		if (found) return;
		std::string temp = nextTempfile();
		callCount++;
		bool res = checker(n, temp);
		returnTempfile(temp);
		if (res && !found) {
			std::lock_guard<std::mutex> guard(resultMutex);
			found = true;
			result = std::make_pair(n, message);
		}
	}
public:
	/**
	 * Constructor.
     * @param tempPrefix Prefix for temporary files.
     */
	Executor(const std::string& tempPrefix): found(false), nextTempId(0), tempPrefix(tempPrefix) {
		reset();
		callCount = 0;
	}
	/**
	 * Destructor.
     */
	~Executor() {
		std::cout << "Overall " << callCount << " calls." << std::endl;
		reset();
	}
	/**
	 * Initiate asynchronous check for the given node.
     * @param n Node to check.
     * @param c Checker.
     * @param message Message.
     */
	void check(Node n, const Checker& c, const std::string& message) {
		if (found) return;
		jobcount++;
		while (jobcount - progress > 100) {
			std::this_thread::sleep_for(std::chrono::milliseconds(50));
		}
		jobs.push(std::async(std::launch::async, &Executor::performCheck, this, n, c, message));
	}
	/**
	 * Wait for at least one job to finish.
     * @return If all jobs have finished.
     */
	bool wait() {
		while (!jobs.empty() && jobs.front().valid()) jobs.pop();
		if (!jobs.empty()) {
			jobs.front().get();
			jobs.pop();
		}
		return jobs.empty();
	}
	/**
	 * Reset this executor.
	 * Waits for all jobs to finish and resets the internal status.
     */
	void reset() {
		while (!jobs.empty()) wait();
		found = false;
		result = std::make_pair(Node(), "");
		jobcount = 0;
		progress = 0;
	}
	/**
	 * Checks if at least one job was successful.
     * @return If a result is there.
     */
	bool hasResult() {
		return found;
	}
	/**
	 * Returns the result, assuming that one exists.
     * @return Result.
     */
	std::pair<Node, std::string> getResult() {
		assert(hasResult());
		return result;
	}
	/**
	 * Returns the current progress.
     * @return Pair of finished and total checks.
     */
	std::pair<unsigned, unsigned> getProgress() const {
		return std::make_pair(progress.load(), jobcount.load());
	}
};

}