/*
 *  SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
 *
 * This file is part of SMT-RAT.
 *
 * SMT-RAT is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMT-RAT is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *
 */


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
	mNrSolved(0),
	mNrSatSolved(0),
	mNrUnsatSolved(0),
	mNrSatInstances(0),
	mNrUnsatInstances(0),
	mAccumulatedTime(0),
	mProduceLaTeX(latex),
	mTimeStamp("")
{
	parseDirectory();
	mNextInstanceToTry = mFilesList.begin();
}
BenchmarkSet::~BenchmarkSet(){}

list<fs::path> BenchmarkSet::pop(unsigned _nrOfExamples)
{
	list<fs::path> result = list<fs::path>();
	if(!done())
	{
		for(unsigned i = 0; i < _nrOfExamples; ++i)
		{
			result.push_back(*mNextInstanceToTry);
			++mNextInstanceToTry;
			if(done())
			{
				return result;
			}
		}
	}
	return result;
}

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

void BenchmarkSet::createTimestamp()
{
	stringstream	timestamp;
	pt::time_facet* facet = new pt::time_facet("%Y%m%dT%H%M%S");
	timestamp.imbue(std::locale(timestamp.getloc(), facet));
	timestamp << pt::second_clock::local_time().date();
	mTimeStamp = timestamp.str();
}

/**
 *
 */
void BenchmarkSet::printSettings() const
{
	BENCHMAX_LOG_INFO("benchmax", "+-");
	BENCHMAX_LOG_INFO("benchmax", "| Benchmark: " << benchmarkName());
	BENCHMAX_LOG_INFO("benchmax", "| Timeout: " << Settings::timeLimit << " seconds");
	//BENCHMAX_LOG_INFO("benchmax", "| Solver: " << solverName());
	BENCHMAX_LOG_INFO("benchmax", "+-");
}

/**
 *
 */
void BenchmarkSet::printResults() const
{
	BENCHMAX_LOG_INFO("benchmax", "**************************************************");
	//BENCHMAX_LOG_INFO("benchmax", "Result: " << solverName() << " solved " << mNrSolved << " out of " << benchmarkCount());
	BENCHMAX_LOG_INFO("benchmax", "sat instances: " << mNrSatSolved << "/" << mNrSatInstances << ", unsat instances: " << mNrUnsatSolved << "/" << mNrUnsatInstances);
	BENCHMAX_LOG_INFO("benchmax", "Accumulated time: " << mAccumulatedTime << " msec");
	BENCHMAX_LOG_INFO("benchmax", "Results: " << mResults);
	BENCHMAX_LOG_INFO("benchmax", "**************************************************");
}

}