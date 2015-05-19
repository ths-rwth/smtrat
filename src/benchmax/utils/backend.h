#pragma once

#include <string>

#include "regex.h"

namespace benchmax {

std::size_t parseDuration(const std::string& output) {
	std::regex re("Start: ([0-9]+).*End: ([0-9]+)", std::regex::extended); //".*End: (\\d+)$");
	std::smatch m;
	if (std::regex_search(output, m, re)) {
		std::size_t p;
		std::size_t start = std::stoull(m[1].str(), &p);
		std::size_t end = std::stoull(m[2].str(), &p);
		return end - start;
	} else {
		return 0;
	}
}

}
