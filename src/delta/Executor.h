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
 * This class generates and reuses temporary filenames with a common prefix.
 */
class TempFilenameGenerator {
private:
	/// Prefix for temporary files.
	std::string prefix;
	/// Mutex for changes to tempfiles.
	std::mutex mutex;
	/// List of temporary files that are available.
	std::queue<std::string> pool;
	/// Id of next temporary file.
	std::atomic<int> nextid;
public:
	/**
	 * Constructor.
     * @param prefix Prefix for all filenames.
     */
	TempFilenameGenerator(const std::string& prefix): prefix(prefix), nextid(0) {}

	/**
	 * Retrieve a filename for a temporary file that is not in use.
     * @return Temporary filename.
     */
	std::string get() {
		std::lock_guard<std::mutex> guard(mutex);
		if (pool.empty()) {
			std::stringstream ss;
			ss << prefix << "-" << nextid++;
			return ss.str();
		}
		auto r = pool.front();
		pool.pop();
		return r;
	}
	/**
	 * Returns a filename to the pool of available filenames.
     * @param temp Temporary filename.
     */
	void refund(const std::string& temp) {
		std::lock_guard<std::mutex> guard(mutex);
		pool.push(temp);
	}
};

/**
 * This class takes care of asynchronous execution of calls to the solver.
 */
class Executor {
private:
	/// Filename generator.
	TempFilenameGenerator temp;
	/// List of job results not checked yet.
	std::queue<std::future<void>> jobs;
	/// Flag if a call was successful.
	std::atomic<bool> found;
	/// Mutex for changes to result.
	std::mutex resultMutex;
	/// Result of successful call, consisting of node and message.
	std::pair<Node, std::string> result;
	/// Number of jobs that have been started.
	std::atomic<unsigned> jobcount;
	/// Number of jobs that have terminated.
	std::atomic<unsigned> progress;
	/// Number of actual calls to the solver.
	std::atomic<unsigned> callCount;

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
		std::string tmp = temp.get();
		callCount++;
		bool res = checker(n, tmp);
		temp.refund(tmp);
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
	Executor(const std::string& tempPrefix): temp(tempPrefix), found(false) {
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