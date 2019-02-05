#pragma once

#include <chrono>
#include <iostream>
#include <map>

namespace benchmax {

/**
 * Results for a single benchmark run.
 */
struct BenchmarkResult {
	/// Shell exit code.
	int exitCode;
	/// Runtime in milliseconds.
	std::chrono::milliseconds time;
	/// Answer string.
	std::string answer;
	/// Standard output (mostly for parsing the answer and dditional information).
	std::string stdout;
	/// Error output (mostly for parsing the answer and dditional information).
	std::string stderr;
	/// Arbitrary additional information that can be provided by the tool class.
	std::map<std::string, std::string> additional;
	
	/**
	 * Properly detect timeouts.
	 * Most backends give processes a bit more time to avoid having race-condition-like situations.
	 */
	template<typename TimeLimit>
	void cleanup(const TimeLimit& limit) {
		if (time > limit) {
			answer = "timeout";
		}
		stdout = "";
		stderr = "";
	}
};

/// Streaming operator for BenchmarkResult.
inline std::ostream& operator<<(std::ostream& os, const BenchmarkResult& results) {
	os << "(" << results.answer << ", " << results.exitCode << ", " << results.time.count() << "ms)" << std::endl;
	os << results.stdout << std::endl;
	os << results.stderr << std::endl;
	return os;
}


}
