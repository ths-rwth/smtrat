/**
 * @file Results.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <map>
#include <mutex>
#include <utility>
#include <vector>

#include "../logging.h"
#include "../BenchmarkStatus.h"
#include "Database.h"
#include "XMLWriter.h"
#include "BenchmarkResult.h"

namespace benchmax {

class Results {
private:
	std::mutex mMutex;
	std::map<const Tool*, std::size_t> mTools;
	std::map<fs::path, std::size_t> mFiles;
	std::map<std::pair<std::size_t,std::size_t>, BenchmarkResult> mResults;
public:
	void addResult(const Tool* tool, const fs::path& file, const BenchmarkResult& results) {
		std::lock_guard<std::mutex> lock(mMutex);
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
	
	void store(Database& db) {
		std::map<std::size_t, std::size_t> toolIDs;
		std::map<std::size_t, std::size_t> fileIDs;
		
		for (const auto& it: mTools) {
			toolIDs[it.second] = db.getToolID(it.first);
			std::cout << toolIDs << std::endl;
		}
		for (const auto& it: mFiles) {
			fileIDs[it.second] = db.getFileID(it.first);
		}
		std::size_t benchmarkID = db.createBenchmark();
		for (const auto& it: mResults) {
			std::size_t tool = toolIDs[it.first.first];
			std::size_t file = fileIDs[it.first.second];
			std::size_t id = db.addBenchmarkResult(benchmarkID, tool, file, it.second.exitCode, it.second.time);
			for (const auto& attr: it.second.additional) {
				db.addBenchmarkAttribute(id, attr.first, attr.second);
			}
		}
	}
	
	void store(XMLWriter& xml) {
		xml.write(mTools, mFiles, mResults);
	}
	
	~Results() {}
};

}
