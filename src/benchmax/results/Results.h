/**
 * @file Results.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <functional>
#include <map>
#include <mutex>
#include <optional>
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
	std::mutex mMutex;
	std::map<const Tool*, std::size_t> mTools;
	std::map<fs::path, std::size_t> mFiles;
	std::map<std::pair<std::size_t,std::size_t>, BenchmarkResult> mData;
public:
	std::optional<std::reference_wrapper<const BenchmarkResult>> get(const Tool* tool, const fs::path& file) const {
		auto toolIt = mTools.find(tool);
		if (toolIt == mTools.end()) return std::nullopt;
		auto fileIt = mFiles.find(file);
		if (fileIt == mFiles.end()) return std::nullopt;
		auto dataIt = mData.find(std::make_pair(toolIt->second, fileIt->second));
		if (dataIt == mData.end()) return std::nullopt;
		return std::ref(dataIt->second);
	}
	const auto& data() const {
		return mData;
	}
	/// Add a new result.
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
		mData.emplace(std::make_pair(toolIt->second, fileIt->second), results);
	}
	
	/// Store all results to some database.
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

		for (const auto& it: mData) {
			std::size_t tool = toolIDs[it.first.first];
			std::size_t file = fileIDs[it.first.second];
			std::size_t id = db.addBenchmarkResult(benchmarkID, tool, file, it.second.exitCode, std::size_t(std::chrono::milliseconds(it.second.time).count()));
			for (const auto& attr: it.second.additional) {
				db.addBenchmarkAttribute(id, attr.first, attr.second);
			}
		}
	}
	
	/// Store all results to a xml file.
	void store(XMLWriter& xml, const Jobs& jobs) const {
		xml.write(jobs, *this);
	}
};

}
