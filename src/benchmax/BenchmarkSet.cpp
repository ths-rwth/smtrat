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
#include "BenchmarkStatus.h"
#include "config.h"
#include "Smt2Input.h"
#include "logging.h"
#include "Settings.h"

#include "../cli/config.h"
#ifdef __VS
#pragma warning(push, 0)
#include <boost/filesystem.hpp>
#pragma warning(pop)
#else
#include <boost/filesystem.hpp>
#endif

namespace dt = boost:: date_time;
namespace pt = boost:: posix_time;
namespace ch = boost:: chrono;

using std::endl;
using carl::Formula;

namespace benchmax {

BenchmarkSet::BenchmarkSet(const fs::path& path,
					 bool latex):
	mPathToDirectory(path),
	mFilesList(),
	mNrSatSolved(0),
	mNrUnsatSolved(0),
	mNrSatInstances(0),
	mNrUnsatInstances(0)
{
	parseDirectory();
	mNextInstanceToTry = mFilesList.begin();
}
BenchmarkSet::~BenchmarkSet(){}

/**
 *
 * @return
 */
int BenchmarkSet::parseDirectory()
{
	fs::path p(mPathToDirectory);
	try
	{
		// does p actually exist?
		if(fs::exists(p))
		{
			// If it is a directory, we add all the contents
			if(fs::is_directory(p))
			{
				std::copy(fs::directory_iterator(p), fs::directory_iterator(), back_inserter(mFilesList));
				// Remove all files but those with the right extension.
				mFilesList.sort();
				BENCHMAX_LOG_DEBUG("benchmax", p << " is a directory containing " << mFilesList);
			}
			// Not a directory, so (we assume?) it is a file.
			else
			{
				mFilesList.push_back(p);
			}
		}
		else BENCHMAX_LOG_WARN("benchmax", p << " does not exist.");
	}
	catch(const fs::filesystem_error& ex)
	{
		BENCHMAX_LOG_ERROR("benchmax", "Filesystem error: " << ex.what());
		return 1;
	}
	return 0;
}

}
