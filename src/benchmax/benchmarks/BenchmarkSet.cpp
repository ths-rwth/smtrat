#include "BenchmarkSet.h"

#include <benchmax/logging.h>
#include <benchmax/utils/filesystem.h>

#include <algorithm>
#include <string>

namespace benchmax {

void BenchmarkSet::add_recursive(const std::filesystem::path& path) {
	try {
		// does p actually exist?
		if(std::filesystem::exists(path))
		{
			if (std::filesystem::is_directory(path)) {
				// If it is a directory, we add all the contents
				BENCHMAX_LOG_TRACE("benchmax", path << " is a directory.");
				for (auto it = std::filesystem::directory_iterator(path); it != std::filesystem::directory_iterator(); it++) {
					add_recursive(*it);
				}
			} else if (std::filesystem::is_symlink(path)) {
				// A symlink. Resolve symlink and call recursively.
				auto r = std::filesystem::read_symlink(path);
				BENCHMAX_LOG_DEBUG("benchmax", path << " is a symlink to " << r);
				add_recursive(r);
			} else {
				// Not a directory, so (we assume?) it is a file.
				mFilesList.push_back(std::filesystem::absolute(path));
			}
		}
		else {
			BENCHMAX_LOG_WARN("benchmax", path << " does not exist.");
		}
	} catch(const std::filesystem::filesystem_error& ex) {
		BENCHMAX_LOG_ERROR("benchmax", "Filesystem error: " << ex.what());
	}
}

void BenchmarkSet::add_directory(const std::filesystem::path& dir) {
	BENCHMAX_LOG_DEBUG("benchmax.benchmarks", "Adding benchmarks from " << dir);
	add_recursive(dir);
	std::sort(mFilesList.begin(), mFilesList.end());
	BENCHMAX_LOG_DEBUG("benchmax.benchmarks", "Now we have " << mFilesList.size() << " benchmarks");
}

}
