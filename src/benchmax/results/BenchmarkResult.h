#pragma once

#include <chrono>
#include <iostream>
#include <map>

namespace benchmax {

struct BenchmarkResult {
	int exitCode;
	std::chrono::milliseconds time;
	std::string stdout;
	std::string stderr;
	std::map<std::string, std::string> additional;
};

inline std::ostream& operator<<(std::ostream& os, const BenchmarkResult& results) {
	os << "(" << results.exitCode << ", " << results.time.count() << "ms)" << std::endl;
	os << results.stdout << std::endl;
	os << results.stderr << std::endl;
	return os;
}


}
