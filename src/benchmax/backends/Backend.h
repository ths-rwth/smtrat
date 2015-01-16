/**
 * @file Backend.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include "../BenchmarkSet.h"
#include "../Tool.h"
#include "../results/Results.h"

namespace benchmax {

class Backend {
protected:
	std::vector<Tool> mTools;
	std::vector<BenchmarkSet> mBenchmarks;
	Results mResults;
	virtual void execute(const Tool&, const fs::path&) {}
public:
	void addTool(const Tool& t) {
		mTools.push_back(t);
	}
	void addBenchmark(const BenchmarkSet& b) {
		mBenchmarks.push_back(b);
	}
	
	void run() {
		for (const Tool& tool: mTools) {
			for (const BenchmarkSet& set: mBenchmarks) {
				for (const fs::path& file: set) {
					if (tool.canHandle(file)) {
						this->execute(tool, file);
					}
				}
			}
		}
	}
};

}