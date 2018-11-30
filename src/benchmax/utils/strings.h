#pragma once

#include <filesystem>
#include <vector>

namespace benchmax {

inline std::size_t commonPrefixLength(const std::string& s1, const std::string& s2, std::size_t max = 0) {
	std::size_t res = 0;
	while (res < s1.length() && res < s2.length()) {
		if (s1[res] != s2[res]) break;
		if (max > 0 && res == max) break;
		res++;
	}
	return res;
}

inline std::string commonPrefix(const std::vector<std::string>& s) {
	if (s.empty()) return "";
	std::size_t len = s.front().length();
	
	for (std::size_t i = 1; i < s.size(); i++) {
		len = commonPrefixLength(s[i-1], s[i], len);
	}
	return s.front().substr(0, s.front().rfind('/', len-1)+1);
}

inline std::string commonPrefix(const std::initializer_list<std::vector<std::string>>& s) {
	if (s.begin() == s.end()) return "";
	if (s.begin()->empty()) return "";
	std::size_t len = s.begin()->front().length();
	
	for (const auto& sv: s) {
		for (std::size_t i = 1; i < sv.size(); i++) {
			len = commonPrefixLength(sv[i-1], sv[i], len);
		}
	}
	return s.begin()->front().substr(0, s.begin()->front().rfind('/', len-1)+1);
}

inline std::string removePrefix(const std::string& s, const std::string& prefix) {
	return s.substr(prefix.length());
}

inline std::string removeDanglingSlashes(const std::string& s) {
	std::string res = s;
	if (res.front() == '/') res = res.substr(1);
	if (res.back() == '/') res = res.substr(0, res.length() - 1);
	return res;
}

/// Checks whether the extension of the filename is as specified.
inline bool isExtension(const std::filesystem::path& path, const std::string& extension) {
	if (!std::filesystem::is_regular_file(path)) return false;
	return path.extension() == extension;
}

}
