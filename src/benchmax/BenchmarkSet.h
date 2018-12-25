/**
 * @file   Benchmark.h
 * @author Sebastian Junges
 * @author Ulrich Loup
 *
 * @since 2012-02-12
 * @version 2013-04-14
 */

#pragma once

#include <iostream>
#include <vector>

#include <filesystem>
namespace fs = std::filesystem;

namespace benchmax {

class BenchmarkSet {
private:
	fs::path mBaseDir;
	std::vector<fs::path> mFilesList;
	void parseDirectory(const fs::path& dir);
public:
	BenchmarkSet(const fs::path& baseDir);
	std::size_t size() const {
		return mFilesList.size();
	}
	const fs::path& baseDir() const {
		return mBaseDir;
	}
	auto begin() const -> decltype(mFilesList.begin()) {
		return mFilesList.begin();
	}
	auto end() const -> decltype(mFilesList.end()) {
		return mFilesList.end();
	}
};

}
