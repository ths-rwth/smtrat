#pragma once

#include <chrono>
#include <iostream>
#include <map>

namespace benchmax {

struct BenchmarkResult {
	int exitCode;
	std::string status;
	std::chrono::milliseconds time;
	std::string stdout;
	std::string stderr;
	std::map<std::string, std::string> additional;
	
	template<typename Tool, typename TimeLimit>
	void cleanup(const Tool& tool, const TimeLimit& limit) {
		if (time > limit) {
			status = "timeout";
		} else {
			status = tool->getStatus(*this);
		}
	}
};

inline std::ostream& operator<<(std::ostream& os, const BenchmarkResult& results) {
	os << "(" << results.status << ", " << results.exitCode << ", " << results.time.count() << "ms)" << std::endl;
	os << results.stdout << std::endl;
	os << results.stderr << std::endl;
	return os;
}


}
