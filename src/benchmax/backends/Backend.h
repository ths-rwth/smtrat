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
	virtual void startTool(const Tool&) {}
	virtual void execute(const Tool&, const fs::path&) {}
public:
	void run(const std::vector<Tool*>& tools, const std::vector<BenchmarkSet>& benchmarks) {
		for (const Tool* tool: tools) {
			this->startTool(*tool);
			for (const BenchmarkSet& set: benchmarks) {
				for (const fs::path& file: set) {
					if (tool->canHandle(file)) {
						//BENCHMAX_LOG_DEBUG("benchmax", "Calling " << tool->binary().native() << " on " << file.native());
						this->execute(*tool, file);
					}
				}
			}
		}
	}
	virtual ~Backend() {
		//Database db;
		//mResults.store(db);
		XMLWriter xml("stats.xml");
		mResults.store(xml);
	}
};

}
