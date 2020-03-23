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
class Consumer {
private:
	/// Filename generator.
	TempFilenameGenerator temp;
	// Checker object.
	const Checker& checker;
	/// List of job results not checked yet.
	std::queue<std::future<void>> jobs;
	/// Flag if a call was successful.
	std::atomic<bool> found;
	/// Mutex for changes to result.
	std::mutex resultMutex;
	/// Result of successful call, consisting of node, message and number of node.
	std::tuple<Node, std::string, std::size_t> result;
	/// Number of jobs that have been started.
	std::atomic<unsigned> jobcount;
	/// Number of jobs that have terminated.
	std::atomic<unsigned> progress;
	/// Number of jobs to run in parallel.
	std::size_t concurrency;

	/**
	 * Calls the checker and checks the result.
	 * Method that is called by `std::async`.
     * @param n Node to check.
     * @param message Message, if check is successful.
	 * @param num Number of this node in the iteration.
     */
	void performCheck(const Node& n, const std::string& message, std::size_t num) {
		if (hasResult()) {
			progress++;
			return;
		}
		std::string tmp = temp.get();
		bool res = checker(n, tmp);
		temp.put(tmp);
		progress++;
		if (res) {
			std::lock_guard<std::mutex> guard(resultMutex);
			if (!found) result = std::make_tuple(n, message, num);
			found = true;
		}
	}
public:
	/**
	 * Constructor.
     * @param tempPrefix Prefix for temporary files.
     */
	Consumer(const std::string& tempPrefix, std::size_t threads, const Checker& checker): temp(tempPrefix), checker(checker), found(false), concurrency(threads) {
		reset();
		if (concurrency == 0) concurrency = std::thread::hardware_concurrency();
	}
	/**
	 * Destructor.
     */
	~Consumer() {
		reset();
	}
	/**
	 * Initiate asynchronous check for the given node.
     * @param n Node to check.
     * @param message Message.
	 * @param num Number of this node in the iteration.
     */
	void consume(const Node& n, const std::string& message, std::size_t num) {
		if (hasResult()) return;
		while (jobs.size() >= concurrency) {
			while (!jobs.empty() && jobs.front().wait_for(std::chrono::seconds(0)) == std::future_status::ready) jobs.pop();
			std::this_thread::sleep_for(std::chrono::milliseconds(50));
		}
		if (hasResult()) return;
		jobcount++;
		jobs.push(std::async(std::launch::async, &Consumer::performCheck, this, n, message, num));
	}
	/**
	 * Wait for at least one job to finish.
     * @return If all jobs have finished.
     */
	bool wait() {
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
		checker.resetKilled();
		while (!jobs.empty()) wait();
		found = false;
		result = std::make_tuple(Node(), "", 0);
		jobcount = 0;
		progress = 0;
	}
	/**
	 * Checks if at least one job was successful.
     * @return If a result is there.
     */
	bool hasResult() const {
		return found;
	}
	/**
	 * Returns the result, assuming that one exists.
     * @return Result.
     */
	std::tuple<Node, std::string, std::size_t> getResult() {
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
