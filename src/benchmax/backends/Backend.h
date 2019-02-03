/**
 * @file Backend.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <benchmax/benchmarks/BenchmarkSet.h>
#include "../tools/Tools.h"
#include "../results/Results.h"
#include "../settings/Settings.h"

#include <atomic>

namespace benchmax {

class Backend {
private:
	Results mResults;
protected:
	std::size_t mExpectedJobs;
	std::atomic<std::size_t> mFinishedJobs;
	std::atomic<std::size_t> mLastPercent;
	
	Backend(): mExpectedJobs(0), mFinishedJobs(0), mLastPercent(0) {}
	
	virtual void startTool(const Tool*) {}
	virtual void execute(const Tool*, const fs::path&, const fs::path&) {}
	/// Can be called to give information about the current progress, if available.
	void madeProgress(std::size_t files = 1) {
		mFinishedJobs += files;
		std::size_t newPercent = mFinishedJobs * 100 / mExpectedJobs;
		if (newPercent > mLastPercent) {
			mLastPercent = newPercent;
			BENCHMAX_LOG_INFO("benchmax", "Progress: " << mLastPercent << "% (" << mFinishedJobs << " / " << mExpectedJobs << ")");
		}
	}
public:
	void addResult(const Tool* tool, const fs::path& file, const fs::path& baseDir, BenchmarkResult& result) {
		tool->additionalResults(file, result);
		result.cleanup(settings_benchmarks().limit_time);
		mResults.addResult(tool, file, baseDir, result);
	}
	void run(const Tools& tools, const std::vector<BenchmarkSet>& benchmarks) {
		for (const BenchmarkSet& set: benchmarks) {
			mExpectedJobs += tools.size() * set.size();
		}
		for (const auto& tool: tools) {
			this->startTool(tool.get());
			for (const BenchmarkSet& set: benchmarks) {
				for (const fs::path& file: set) {
					if (tool->canHandle(file)) {
						//BENCHMAX_LOG_DEBUG("benchmax", "Calling " << tool->binary().native() << " on " << file.native());
						this->execute(tool.get(), file, set.baseDir());
					}
				}
			}
		}
		BENCHMAX_LOG_INFO("benchmax", "Scheduled all jobs, waiting for termination.");
	}
	virtual ~Backend() {
		//Database db;
		//mResults.store(db);
		BENCHMAX_LOG_INFO("benchmax", "Writing results to " << settings_benchmarks().output_file_xml);
		XMLWriter xml(settings_benchmarks().output_file_xml);
		mResults.store(xml);
	}
};

}
