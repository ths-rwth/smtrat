#pragma once

namespace benchmax {
    inline std::size_t parse_peak_memory(const std::string& output) {
		std::regex regexpr("Maximum resident set size \\(kbytes\\): ([0-9]+)");
		std::smatch base_match;
		bool match = std::regex_search(output, base_match, regexpr);
		assert(match && base_match.size() == 2);
		std::ssub_match base_sub_match = base_match[1];
		std::stringstream ss(base_sub_match.str());
		size_t result;
		ss >> result;
		return result;
	}
}