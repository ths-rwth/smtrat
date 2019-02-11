#pragma once

#include <filesystem>
#include <iostream>
#include <vector>

#include "../logging.h"

namespace benchmax {

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

/**
 * Computes the common prefix of a list of paths.
 * skip_last specifies whether the last part if the path (usually the filename) may be part of the prefix.
 */
inline std::filesystem::path common_prefix(const std::vector<std::filesystem::path>& s, bool skip_last = true) {
	if (s.empty()) return std::filesystem::path();
	auto cur = s.front();
	if (skip_last) {
		cur = cur.parent_path();
	}
	for (std::size_t i = 1; i < s.size(); i++) {
		cur = common_prefix(cur, s[i]);
	}
	return cur;
}

/**
 * Computes the common prefix of multiple lists of paths.
 * skip_last specifies whether the last part if the path (usually the filename) may be part of the prefix.
 */
inline std::filesystem::path common_prefix(const std::initializer_list<std::vector<std::filesystem::path>>& s, bool skip_last = true) {
	std::vector<std::filesystem::path> all;
	for (const auto& sv: s) {
		all.insert(all.end(), sv.begin(), sv.end());
	}
	return common_prefix(all, skip_last);
}

/// Remove a prefix from a path.
inline std::filesystem::path remove_prefix(const std::filesystem::path& s, const std::filesystem::path& prefix) {
	return std::filesystem::relative(s, prefix);
	//return s.substr(prefix.length());
}

/// Checks whether the extension of the filename is as specified.
inline bool is_extension(const std::filesystem::path& path, const std::string& extension) {
	if (!std::filesystem::is_regular_file(path)) return false;
	return path.extension() == extension;
}

}
