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
 * @file   Benchmark.h
 * @author Sebastian Junges
 * @author Ulrich Loup
 *
 * @since 2012-02-12
 * @version 2013-04-14
 */

#pragma once

#include <cstdlib>
#include <stdio.h>
#include <stdlib.h>
#include <string>
#include <sstream>
#include <iostream>

#define BOOST_FILESYSTEM_VERSION 3

#include <boost/chrono/chrono_io.hpp>

//#include <boost/chrono/round.hpp>

#include <boost/filesystem.hpp>
#include <boost/lexical_cast.hpp>
#include <boost/program_options.hpp>
#include <boost/foreach.hpp>
#include <boost/filesystem/fstream.hpp>
#include <boost/date_time.hpp>
#include <boost/date_time/posix_time/ptime.hpp>

#include "Stats.h"
#include "Tool.h"
#include "BenchmarkStatus.h"
#include "Settings.h"

namespace ch = boost::chrono;
namespace fs = boost::filesystem;

//support for rounding for boost 1.47.0
namespace boost
{
	namespace chrono
	{
		template<class To, class Rep, class Period>
		To round(const boost::chrono::duration<Rep, Period>& d)
		{
			To t0 = boost::chrono::duration_cast<To>(d);
			To t1 = t0;
			++t1;
			auto diff0 = d - t0;
			auto diff1 = t1 - d;
			if(diff0 == diff1)
			{
				if(t0.count() & 1)
					return t1;
				return t0;
			}
			else if(diff0 < diff1)
				return t0;
			return t1;
		}
	}
}
typedef std::pair<std::string, std::string> doublestring;

namespace benchmax {

struct FilterFileExtensions
{
	std::string mExt;

	FilterFileExtensions(std::string ext):
		mExt(ext)
	{}

	bool operator ()(const fs::path& value)
	{
		return fs::extension(value) != mExt;
	}
};

class BenchmarkSet
{
	/////////////
	// Members //
	/////////////

	fs::path mPathToDirectory;
	std::list<fs::path> mFilesList;
	std::list<fs::path>::iterator mNextInstanceToTry;
	std::vector<std::pair<std::string, doublestring>> mResults;
	std::size_t mNrSolved;
	std::size_t mNrSatSolved;
	std::size_t mNrUnsatSolved;
	std::size_t mNrSatInstances;
	std::size_t mNrUnsatInstances;
	std::size_t mAccumulatedTime;
	bool mProduceLaTeX;
	std::string mTimeStamp;

	public:

		///////////////////////
		// Con-/Destructors  //
		///////////////////////

		//Benchmark();
		BenchmarkSet(const fs::path&, bool);
		~BenchmarkSet();

		
		
		///////////////
		// Selectors //
		///////////////

		bool produceLaTeX() const
		{
			return mProduceLaTeX;
		}
		std::size_t benchmarkCount() const
		{
			return mFilesList.size();
		}

		std::size_t nrSolved() const
		{
			return mNrSolved;
		}

		std::size_t accumulatedTimeInMillis() const
		{
			return mAccumulatedTime;
		}

		double accumulatedTimeInSecs() const
		{
			return mAccumulatedTime / 1000.0;
		}

		bool done() const
		{
			return mNextInstanceToTry == mFilesList.end();
		}

		const std::string& timeStamp() const
		{
			return mTimeStamp;
		}

		std::string benchmarkName() const
		{
			fs::path p(mPathToDirectory);
			if(fs::is_directory(p))
			{
				return p.parent_path().filename().string();
			}
			else
			{
				return p.parent_path().filename().string();
			}

		}

		/////////////
		// Methods //
		/////////////

		std::list<fs::path> pop(unsigned _nrOfExamples);
		int run();
		
		std::list<fs::path>::const_iterator begin() const {
			return mFilesList.begin();
		}
		std::list<fs::path>::const_iterator end() const {
			return mFilesList.end();
		}

		void printSettings() const;
		void printResults() const;

	protected:
		int parseDirectory();
		void createTimestamp();

};

}
