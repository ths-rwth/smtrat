/**
 * @file   Stats.h
 * @author Sebastian Junges
 * @created 28/11/2012
 *
 */

#pragma once

#include <string>
#include <vector>

namespace benchmax {

class Stats
{
	public:
		enum Type { STATS_COLLECTION, BENCHMARK_RESULT };

	protected:
		Type mType;
		// 1, if collecting; -1, if collecting finished; 0, if not yet collected.
		int mCollectingSolvers;
		int mCollectingBenchmarkSets;
		int mCollectingBenchmarkFiles;
		int mCollectingInputStats;
		int mCollectingRuns;
		int mCollectingRunTimeStats;
		int mCollectingResults;
		// The path to the file write the statistics in.
		std::string mFile;

	public:
		Stats(const std::string&, Type);
		~Stats();

		Type type() const
		{
			return mType;
		}

		const std::string& fileName() const
		{
			return mFile;
		}

		void addBenchmarkSet(const std::string&);
		void addSolver(const std::string&);
		void addBenchmarkFile(const std::string&);
		void addInputStat(const std::string&, const std::string&);
		void addInputStat(const std::string&, int);
		void addRun(const std::string&, std::size_t);
		void addRunTimeStat(const std::string&, const std::string&);
		void addResult(const std::string&, const std::string&, const std::string&);
		void addResult(const std::string&, bool);
		void addStat(const std::string&);

		static void createStatsCompose(const std::string&);
		static void createLatexCompose(const std::string&);
		static void composeStats(const std::vector<std::string>&);
		static void callComposeProcessor(const std::string& io);
		static void callComposeProcessor();

};

}
