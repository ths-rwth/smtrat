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

#define BOOST_FILESYSTEM_VERSION 3
#ifdef __VS
#pragma warning(push, 0)
#include <boost/filesystem.hpp>
#pragma warning(pop)
#else
#include <boost/filesystem.hpp>
#endif
namespace fs = boost::filesystem;

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
