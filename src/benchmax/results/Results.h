/**
 * @file Results.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <map>
#include <mutex>
#include <utility>
#include <vector>

#include <filesystem>

#include "../logging.h"
#include "../tools/Tool.h"
#include "Database.h"
#include "XMLWriter.h"
#include "BenchmarkResult.h"

namespace benchmax {

namespace fs = std::filesystem;

/**
 * Stores results for for whole benchmax run.
 * Allows for (concurrent) insertion of the individual results via addResult().
 * Eventually results can be stored to a database (if enabled) or to a xml file.
 */
class Results {
private:
	struct ResultSet {
		std::map<fs::path, std::size_t> files;
		std::map<std::pair<std::size_t,std::size_t>, BenchmarkResult> data;
	};
	std::mutex mMutex;
	std::map<const Tool*, std::size_t> mTools;
	std::map<fs::path, ResultSet> mResults;
public:
	/// Add a new result.
	void addResult(const Tool* tool, const fs::path& file, const fs::path& baseDir, const BenchmarkResult& results) {
		std::lock_guard<std::mutex> lock(mMutex);
		auto toolIt = mTools.find(tool);
		if (toolIt == mTools.end()) {
			toolIt = mTools.emplace(tool, mTools.size()).first;
		}
		auto& files = mResults[baseDir].files;
		auto fileIt = files.find(file);
		if (fileIt == files.end()) {
			fileIt = files.emplace(file, files.size()).first;
		}
		mResults[baseDir].data.emplace(std::make_pair(toolIt->second, fileIt->second), results);
	}
	
	/// Store all results to some database.
	void store(Database& db) {
		std::map<std::size_t, std::size_t> toolIDs;
		std::map<std::size_t, std::size_t> fileIDs;
		
		for (const auto& it: mTools) {
			toolIDs[it.second] = db.getToolID(it.first);
			std::cout << toolIDs << std::endl;
		}
		std::size_t benchmarkID = db.createBenchmark();
		for (const auto& set: mResults) {
			for (const auto& it: set.second.files) {
				fileIDs[it.second] = db.getFileID(it.first);
			}
			for (const auto& it: set.second.data) {
				std::size_t tool = toolIDs[it.first.first];
				std::size_t file = fileIDs[it.first.second];
				std::size_t id = db.addBenchmarkResult(benchmarkID, tool, file, it.second.exitCode, std::size_t(std::chrono::milliseconds(it.second.time).count()));
				for (const auto& attr: it.second.additional) {
					db.addBenchmarkAttribute(id, attr.first, attr.second);
				}
			}
		}
	}
	
	/// Store all results to a xml file.
	void store(XMLWriter& xml) {
		xml.write(mTools, mResults);
	}
};

}
