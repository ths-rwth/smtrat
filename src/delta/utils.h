/**
 * @file utils.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <atomic>
#include <cassert>
#include <cstdio>
#include <iostream>
#include <mutex>
#include <queue>
#include <utility>

namespace delta {

	
/// Terminal code for bold red font.
#define BRED "\033[1;31m"
/// Terminal code for bold green font.
#define BGREEN "\033[1;32m"
/// Terminal code for green font.
#define GREEN "\033[0;32m"
/// Terminal code for gray font.
#define GRAY "\033[0;37m"
/// Terminal code for default font.
#define END "\033[0;39m"
/// Terminal code to clear the previous line.
#define CLEARLINE "\033[1F\033[1K"

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
	 * Destructor.
     */
	~TempFilenameGenerator() {
		while (!pool.empty()) {
			std::remove(pool.front().c_str());
			pool.pop();
		}
	}

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
	void put(const std::string& temp) {
		std::lock_guard<std::mutex> guard(mutex);
		pool.push(temp);
	}
};

/**
 * This class provides a simple way to show progress bars on the command line.
 */
class ProgressBar {
private:
	/// Current total.
	std::size_t total;
	/// Current progress.
	std::size_t progress;
public:
	/**
	 * Increase progress by one and show progress bar.
     */
	void operator()() {
		progress++;
		(*this)(progress, total);
	}
	/**
	 * Increase progress by number of steps and show progress bar.
	 * @param steps Steps to move forward.
	 */
	void operator()(std::size_t steps) {
		progress += steps;
		(*this)(progress, total);
	}
	/**
	 * Print a progress bar for a progress of `progress / total`.
	 * @param p Progress.
	 */
	void operator()(const std::pair<std::size_t, std::size_t>& p) {
		if (p.second != 0) (*this)(p.first, p.second);
	}
	/**
	 * Print a progress bar for a progress of `progress / total`.
	 * @param progress Progress.
	 * @param total Total.
	 */
	void operator()(std::size_t progress, std::size_t total) {
		assert(total != 0);
		this->total = total;
		this->progress = progress;
		std::size_t size = progress*30 / total;
		if ((size == ((progress-1)*30 / total)) && (progress % 5 != 0)) return;
		if (progress > 0) std::cout << CLEARLINE;
		std::cout << "[" << std::string(size, '=') << std::string(30 - size, ' ') << "] (" << progress << " / " << total << ")" << std::endl;
	}
};

/**
 * This class can be used to create `std::string` objects using streaming operators.
 */
class String {
private:
	/// Internal buffer.
	std::stringstream s;
public:
	/**
	 * Add some data to the string.
     * @param t Data.
     * @return `*this`
     */
	template<typename T>
	String& operator<<(const T& t) {
		s << t;
		return *this;
	}
	/**
	 * Return data as string.
     * @return Data as string.
     */
	operator std::string() const {
		return s.str();
    }
};

}