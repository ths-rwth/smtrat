#pragma once

#include <vector>

namespace benchmax {
	
inline std::string commonPrefix(const std::vector<std::string>& s) {
	if (s.empty()) return "";
	std::size_t len = s.front().length();
	
	for (std::size_t i = 1; i < s.size(); i++) {
		if (len > s[i].length()) len = s[i].length();
		for (std::size_t j = 0; j < len; j++) {
			if (s.front()[j] != s[i][j]) {
				len = j;
				break;
			}
		}
	}
	return s.front().substr(0, s.front().rfind('/', len-1)+1);
}

inline std::string removePrefix(const std::string& s, const std::string& prefix) {
	return s.substr(prefix.length());
}

}
