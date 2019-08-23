/**
 * @file Backend.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include "../results/Results.h"
#include "../settings/Settings.h"
#include "Jobs.h"

#include <atomic>

namespace benchmax {

/**
 * Base class for all backends.
 * Offers appropriate hooks to model the whole workflow for backends where each job is executed individually.
 * The run() method is called from ourside which first calls startTool() for every tool and then runs execute() for every pair of tool and benchmark.
 * It also offers addResult() to store results and madeProgress() to provide a progress indication to the user.
 * If a benchmark requires a completely different workflow, for example for a batch job, it should override the run() method.
 */
class Backend {
private:
	/// Results of already completed jobs.
	Results mResults;
protected:
	/// Number of jobs that should be run.
	std::size_t mExpectedJobs;
	/// Number of jobs that are finished.
	std::atomic<std::size_t> mFinishedJobs;
	/// Percentage of finished jobs when madeProgress() was last called.
	std::atomic<std::size_t> mLastPercent;
	
	Backend(): mExpectedJobs(0), mFinishedJobs(0), mLastPercent(0) {}
	
	/**
	 * Hook for every tool at the beginning.
	 * Can be used to upload the tool to some remote system.
	 */
	virtual void startTool(const Tool*) {}
	/**
	 * Hook to allow for asynchronous backends to wait for jobs to terminate.
	 */
	virtual void finalize() {};
	/**
	 * Execute a single pair of tool and benchmark.
	 */
	virtual void execute(const Tool*, const fs::path&) {}
	/// Can be called to give information about the current progress, if available.
	void madeProgress(std::size_t files = 1) {
		mFinishedJobs += files;
		std::size_t newPercent = mFinishedJobs * 100 / mExpectedJobs;
		if (newPercent > mLastPercent) {
			mLastPercent = newPercent;
			BENCHMAX_LOG_INFO("benchmax", "Progress: " << mLastPercent << "% (" << mFinishedJobs << " / " << mExpectedJobs << ")");
		}
	}

	virtual bool collect_results(bool check_finished) {}
	void sanitize_results(const Jobs& jobs) const {
		for (const auto& j: jobs) {
			auto res = mResults.get(j.first, j.second);
			if (!res && j.first->canHandle(j.second)) {
				BENCHMAX_LOG_WARN("benchmax", "Missing result for " << j.first->name() << " on " << j.second);
				BENCHMAX_LOG_WARN("benchmax", "Chances are that something went wrong, please check this!");
			}
		}
	}
	void write_results(const Jobs& jobs) const {
		BENCHMAX_LOG_INFO("benchmax", "Writing results to " << settings_benchmarks().output_file_xml);
		XMLWriter xml(settings_benchmarks().output_file_xml);
		mResults.store(xml, jobs);
	}

public:
	bool suspendable() const {
		return false;
	}
	void process_results(const Jobs& jobs, bool check_finished) {
		if (collect_results(check_finished)) {
			sanitize_results(jobs);
			write_results(jobs);
		} else {
			BENCHMAX_LOG_WARN("benchmax", "Aborted.");
		}
	}
	/// Add a result.
	void addResult(const Tool* tool, const fs::path& file, BenchmarkResult& result) {
		tool->additionalResults(file, result);
		if (result.time > settings_benchmarks().limit_time + 2*settings_benchmarks().grace_time) {
			BENCHMAX_LOG_WARN("benchmax", "Computation took longer than it should: " << carl::settings::duration(result.time) << " > " << settings_benchmarks().limit_time << " + " << settings_benchmarks().grace_time);
			BENCHMAX_LOG_WARN("benchmax", "Offending command: " << tool->name() << " " << file);
		}
		result.cleanup(settings_benchmarks().limit_time);
		mResults.addResult(tool, file, result);
	}
	/// Run the list of tools against the list of benchmarks.
	void run(const Jobs& jobs, bool wait_for_termination) {
		mExpectedJobs = jobs.size();
		BENCHMAX_LOG_INFO("benchmax", "Running " << mExpectedJobs << " now.");
		if (!wait_for_termination) {
			BENCHMAX_LOG_INFO("benchmax", "Running jobs synchronously.");
		}

		for (const auto& tool: jobs.tools()) {
			this->startTool(tool.get());
		}
		for (const auto& [tool, file]: jobs.randomized()) {
			this->execute(tool, file);
		}
		this->finalize();
	}
};

}
