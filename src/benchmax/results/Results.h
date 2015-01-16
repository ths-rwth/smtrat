/**
 * @file Stats.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <map>
#include <utility>
#include <vector>

#include "../BenchmarkStatus.h"

namespace benchmax {

class Results {
private:
	std::map<Tool, std::size_t> mTools;
	std::map<fs::path, std::size_t> mFiles;
	std::map<std::pair<std::size_t,std::size_t>, BenchmarkResults> mResults;
public:
	void addResult(const Tool& tool, const fs::path& file, const BenchmarkResults& results) {
		auto toolIt = mTools.find(tool);
		if (toolIt == mTools.end()) {
			toolIt = mTools.emplace(tool, mTools.size()).first;
		}
		auto fileIt = mFiles.find(file);
		if (fileIt == mFiles.end()) {
			fileIt = mFiles.emplace(file, mFiles.size()).first;
		}
		mResults.emplace(std::make_pair(toolIt->second, fileIt->second), results);
	}
};

}