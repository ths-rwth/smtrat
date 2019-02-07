#pragma once

#include <filesystem>
#include <iostream>
#include <vector>

#include "../logging.h"

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

/// Computes the common prefix of two paths.
inline std::filesystem::path common_prefix(const std::filesystem::path& p1, const std::filesystem::path& p2) {
	std::filesystem::path result;
	for (
		auto it1 = p1.begin(), it2 = p2.begin();
		it1 != p1.end() && it2 != p2.end();
		++it1, ++it2)
	{
		if (*it1 != *it2) break;
		result /= *it1;
	}
	return result;
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
	auto cur = s.front().parent_path();
	for (std::size_t i = 1; i < s.size(); i++) {
		cur = common_prefix(cur, s[i]);
	}
	return cur;
}

/// Computes the common prefix of multiple lists of strings.
inline std::filesystem::path common_prefix(const std::initializer_list<std::vector<std::filesystem::path>>& s) {
	std::vector<std::filesystem::path> all;
	for (const auto& sv: s) {
		all.insert(all.end(), sv.begin(), sv.end());
	}
	return common_prefix(all);
}

/// Remove a prefix from a path.
inline std::filesystem::path remove_prefix(const std::filesystem::path& s, const std::filesystem::path& prefix) {
	return std::filesystem::relative(s, prefix);
	//return s.substr(prefix.length());
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

/// Make all paths canonical.
inline void make_canonical(std::vector<std::filesystem::path>& paths) {
	for (auto& p : paths) {
		std::cout << "Make " << p << " canonical" << std::endl;
		p = std::filesystem::canonical(p);
	}
}

}
