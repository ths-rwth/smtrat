/**
 * @file   Benchmark.h
 * @author Sebastian Junges
 * @author Ulrich Loup
 *
 * @since 2012-02-12
 * @version 2013-04-14
 */

#pragma once

#include <filesystem>
#include <iostream>
#include <vector>

namespace benchmax {

class BenchmarkSet {
private:
	std::filesystem::path mBaseDir;
	std::vector<std::filesystem::path> mFilesList;
	void parseDirectory(const std::filesystem::path& dir);
public:
	BenchmarkSet(const std::filesystem::path& baseDir);
	std::size_t size() const {
		return mFilesList.size();
	}
	const std::filesystem::path& baseDir() const {
		return mBaseDir;
	}
	auto begin() const {
		return mFilesList.begin();
	}
	auto end() const {
		return mFilesList.end();
	}
};

}
