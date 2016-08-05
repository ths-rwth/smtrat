/**
 * @file   BenchmarkSet.cpp
 * @author Sebastian Junges
 * @author Florian Corzilius
 * @author Ulrich Loup
 *
 * @since 2012-12-11
 * @version 2013-05-03
 */

#include "BenchmarkSet.h"
#include "logging.h"

#include <string>

namespace benchmax {

BenchmarkSet::BenchmarkSet(const fs::path& baseDir): mBaseDir(baseDir), mFilesList() {
	parseDirectory(mBaseDir);
}

void BenchmarkSet::parseDirectory(const fs::path& dir)
{
	try {
		// does p actually exist?
		if(fs::exists(dir))
		{
			if (fs::is_directory(dir)) {
				// If it is a directory, we add all the contents
				BENCHMAX_LOG_DEBUG("benchmax", dir << " is a directory.");
				for (auto it = fs::directory_iterator(dir); it != fs::directory_iterator(); it++) {
					parseDirectory(*it);
				}
			} else if (fs::is_symlink(dir)) {
				// A symlink. Resolve symlink and call recursively.
				fs::path r = fs::read_symlink(dir);
				BENCHMAX_LOG_DEBUG("benchmax", dir << " is a symlink to " << r);
				parseDirectory(r);
			} else {
				// Not a directory, so (we assume?) it is a file.
				mFilesList.push_back(dir);
			}
		}
		else BENCHMAX_LOG_WARN("benchmax", dir << " does not exist.");
	} catch(const fs::filesystem_error& ex) {
		BENCHMAX_LOG_ERROR("benchmax", "Filesystem error: " << ex.what());
	}
}

}
