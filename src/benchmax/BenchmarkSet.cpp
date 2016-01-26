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


namespace benchmax {

BenchmarkSet::BenchmarkSet(const fs::path& baseDir): mFilesList() {
	parseDirectory(baseDir);
}

void BenchmarkSet::parseDirectory(const fs::path& dir)
{
	try
	{
		// does p actually exist?
		if(fs::exists(dir))
		{
			// If it is a directory, we add all the contents
			if(fs::is_directory(dir))
			{
				std::copy(fs::directory_iterator(dir), fs::directory_iterator(), back_inserter(mFilesList));
				// Remove all files but those with the right extension.
				std::sort(mFilesList.begin(), mFilesList.end());
				BENCHMAX_LOG_DEBUG("benchmax", dir << " is a directory containing " << mFilesList);
			}
			// Not a directory, so (we assume?) it is a file.
			else
			{
				mFilesList.push_back(dir);
			}
		}
		else BENCHMAX_LOG_WARN("benchmax", dir << " does not exist.");
	}
	catch(const fs::filesystem_error& ex)
	{
		BENCHMAX_LOG_ERROR("benchmax", "Filesystem error: " << ex.what());
	}
}

}
