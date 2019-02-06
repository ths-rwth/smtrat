#pragma once

#include <filesystem>
#include <vector>

namespace benchmax {

/// Computes the length of the common prefix of two strings.
inline std::size_t common_prefix_length(const std::string& s1, const std::string& s2, std::size_t max = 0) {
	std::size_t res = 0;
	while (res < s1.length() && res < s2.length()) {
		if (s1[res] != s2[res]) break;
		if (max > 0 && res == max) break;
		res++;
	}
	return res;
}

/// Computes the common prefix of a list of strings.
inline std::string common_prefix(const std::vector<std::string>& s) {
	if (s.empty()) return "";
	std::size_t len = s.front().length();
	
	for (std::size_t i = 1; i < s.size(); i++) {
		len = common_prefix_length(s[i-1], s[i], len);
	}
	return s.front().substr(0, s.front().rfind('/', len-1)+1);
}

/// Computes the common prefix of a list of paths.
inline std::filesystem::path common_prefix(const std::vector<std::filesystem::path>& s) {
	if (s.empty()) return std::filesystem::path();
	const auto& front = s.front().native();
	std::size_t len = front.length();
	
	for (std::size_t i = 1; i < s.size(); i++) {
		len = common_prefix_length(s[i-1].native(), s[i].native(), len);
	}
	return front.substr(0, front.rfind('/', len-1)+1);
}

/// Computes the common prefix of multiple lists of strings.
inline std::string common_prefix(const std::initializer_list<std::vector<std::string>>& s) {
	if (s.begin() == s.end()) return "";
	if (s.begin()->empty()) return "";
	std::size_t len = s.begin()->front().length();
	
	for (const auto& sv: s) {
		for (std::size_t i = 1; i < sv.size(); i++) {
			len = common_prefix_length(sv[i-1], sv[i], len);
		}
	}
	return s.begin()->front().substr(0, s.begin()->front().rfind('/', len-1)+1);
}

/// Remove a prefix from a string.
inline std::string remove_prefix(const std::string& s, const std::string& prefix) {
	return s.substr(prefix.length());
}

/// Checks whether the extension of the filename is as specified.
inline bool is_extension(const std::filesystem::path& path, const std::string& extension) {
	if (!std::filesystem::is_regular_file(path)) return false;
	return path.extension() == extension;
}

}
