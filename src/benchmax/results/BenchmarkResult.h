#pragma once

#include <iostream>
#include <map>

namespace benchmax {

struct BenchmarkResult {
	int exitCode;
	std::size_t time;
	std::string stdout;
	std::string stderr;
	std::map<std::string, std::string> additional;
};

inline std::ostream& operator<<(std::ostream& os, const BenchmarkResult& results) {
	os << "(" << results.exitCode << ", " << results.time << ")" << std::endl;
	os << results.stdout << std::endl;
	os << results.stderr << std::endl;
	return os;
}


}
