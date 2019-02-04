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
	/// Common base directory.
	std::filesystem::path mBaseDir;
	/// List of files in this benchmark set.
	std::vector<std::filesystem::path> mFilesList;
	/// Recursively find all benchmarks from this directory.
	void parse_directory(const std::filesystem::path& dir);
public:
	/// Constructs BenchmarkSet with all files from the given directory.
	BenchmarkSet(const std::filesystem::path& baseDir);
	/// Number of files.
	std::size_t size() const {
		return mFilesList.size();
	}
	/// Base directory.
	const std::filesystem::path& baseDir() const {
		return mBaseDir;
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
