#pragma once

#include <filesystem>
#include <iostream>
#include <vector>

namespace benchmax {

/**
 * A set of benchmarks from some common base directory.
 */
class BenchmarkSet {
private:
	/// List of files in this benchmark set.
	std::vector<std::filesystem::path> mFilesList;
public:
	/// Recursively find all benchmarks from this directory.
	void add_directory(const std::filesystem::path& dir);
	/// Number of files.
	std::size_t size() const {
		return mFilesList.size();
	}
	/// Begin iterator.
	auto begin() const {
		return mFilesList.begin();
	}
	/// End iterator.
	auto end() const {
		return mFilesList.end();
	}
};

}
