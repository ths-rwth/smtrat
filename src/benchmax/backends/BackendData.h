/**
 * @file Backend.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <map>
#include <set>
#include <vector>

#include "../logging.h"
#include "../BenchmarkSet.h"
#include "../Stats.h"

#include "../tools/Tool.h"

namespace benchmax {

struct BackendData {
	
	
	std::map<std::pair<std::string, std::string>, benchmax::BenchmarkSet*> table;
	std::set<std::string> solverSet;
	std::set<std::string> benchmarkSet;
	std::vector<benchmax::BenchmarkSet*> benchmarks;
	Stats* stats;
	
	BackendData(): stats(nullptr) {}
	~BackendData() {
		for (auto& it: benchmarks) delete it;
		benchmarks.clear();
		delete stats;
	}
};

}
