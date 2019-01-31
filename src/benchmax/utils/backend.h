#pragma once

#include <regex>
#include <string>

#include "durations.h"

namespace benchmax {

std::chrono::milliseconds parseDuration(const std::string& output) {
	std::regex re("Start: ([0-9]+).*End: ([0-9]+)", std::regex::extended); //".*End: (\\d+)$");
	std::smatch m;
	if (std::regex_search(output, m, re)) {
		std::size_t p;
		std::size_t start = std::stoull(m[1].str(), &p);
		std::size_t end = std::stoull(m[2].str(), &p);
		return std::chrono::milliseconds(end - start);
	} else {
		return std::chrono::milliseconds(0);
	}
}

}
