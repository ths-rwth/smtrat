#include "BenchmarkSet.h"

#include <benchmax/logging.h>
#include <benchmax/utils/filesystem.h>

#include <algorithm>
#include <string>

namespace benchmax {

void BenchmarkSet::add_directory(const std::filesystem::path& dir) {
	try {
		// does p actually exist?
		if(std::filesystem::exists(dir))
		{
			if (std::filesystem::is_directory(dir)) {
				// If it is a directory, we add all the contents
				BENCHMAX_LOG_TRACE("benchmax", dir << " is a directory.");
				for (auto it = std::filesystem::directory_iterator(dir); it != std::filesystem::directory_iterator(); it++) {
					add_directory(*it);
				}
			} else if (std::filesystem::is_symlink(dir)) {
				// A symlink. Resolve symlink and call recursively.
				auto r = std::filesystem::read_symlink(dir);
				BENCHMAX_LOG_DEBUG("benchmax", dir << " is a symlink to " << r);
				add_directory(r);
			} else {
				// Not a directory, so (we assume?) it is a file.
				mFilesList.push_back(std::filesystem::absolute(dir));
			}
		}
		else {
			BENCHMAX_LOG_WARN("benchmax", dir << " does not exist.");
		}
	} catch(const std::filesystem::filesystem_error& ex) {
		BENCHMAX_LOG_ERROR("benchmax", "Filesystem error: " << ex.what());
	}
	std::sort(mFilesList.begin(), mFilesList.end());
}

}
