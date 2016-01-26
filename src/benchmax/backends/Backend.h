/**
 * @file Backend.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include "../BenchmarkSet.h"
#include "../tools/Tool.h"
#include "../utils/regex.h"
#include "../results/Results.h"

namespace benchmax {

class Backend {
protected:
	Results mResults;
	std::size_t mExpectedJobs;
	std::atomic<std::size_t> mFinishedJobs;
	
	Backend(): mExpectedJobs(0), mFinishedJobs(0) {}
	
	virtual void startTool(const Tool*) {}
	virtual void execute(const Tool*, const fs::path&) {}
	void madeProgress() {
		mFinishedJobs += 1;
		BENCHMAX_LOG_INFO("benchmax", "Progress: " << mFinishedJobs << " / " << mExpectedJobs);
	}
public:
	void run(const std::vector<Tool*>& tools, const std::vector<BenchmarkSet>& benchmarks) {
		for (const Tool* tool: tools) {
			this->startTool(tool);
			for (const BenchmarkSet& set: benchmarks) {
				mExpectedJobs += set.size();
				for (const fs::path& file: set) {
					if (tool->canHandle(file)) {
						//BENCHMAX_LOG_DEBUG("benchmax", "Calling " << tool->binary().native() << " on " << file.native());
						this->execute(tool, file);
					}
				}
			}
		}
		BENCHMAX_LOG_INFO("benchmax", "Scheduled all jobs, waiting for termination.");
	}
	virtual ~Backend() {
		//Database db;
		//mResults.store(db);
		BENCHMAX_LOG_INFO("benchmax", "Writing results to " << Settings::StatsXMLFile);
		XMLWriter xml(Settings::StatsXMLFile);
		mResults.store(xml);
	}
};

}
