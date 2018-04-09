/**
 * @file Database.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <boost/filesystem.hpp>

#ifdef BENCHMAX_DATABASE
// Include exactly one implementation.
#include "Database_mysqlconnector.h"
//#include "Database_mysqlpp.h"
#endif

#include "../logging.h"
#include "../tools/Tool.h"

namespace benchmax {

namespace fs = boost:: filesystem;

#ifdef BENCHMAX_DATABASE
class Database {
	DBAL conn;
public:
	
	typedef DBAL::Index Index;
	
	Index addTool(const Tool* tool) {
		Index id = conn.insert("INSERT INTO main_tool (`interface`, `hash`) VALUES (%0q, %1q)", tool->name(), tool->attributeHash());
		DBAL::Statement stmt = conn.prepare("INSERT INTO main_toolattribute (`key`, `value`, `tool_id`) VALUES (%0q, %1q, %2q)");
		for (const auto& it: tool->attributes()) {
			conn.execute(stmt, it.first, it.second, id);
		}
		return id;
	}
	
	Index getToolID(const Tool* tool) {
		DBAL::Results res = conn.select("SELECT id FROM main_tool WHERE `interface` = %0q AND `hash` = %1q", tool->name(), tool->attributeHash());
		if (conn.size(res) == 0) {
			return addTool(tool);
		}
		assert(conn.size(res) == 1);
		return conn.getIndex(res, "id");
	}
	
	Index addFile(const fs::path& file) {
		return conn.insert("INSERT INTO main_file (`filename`) VALUES (%0q)", file.native());
	}
	
	Index getFileID(const fs::path& file) {
		DBAL::Results res = conn.select("SELECT id FROM main_file WHERE `filename` = %0q", file.native());
		if (conn.size(res) == 0) {
			return addFile(file);
		}
		assert(conn.size(res) == 1);
		return conn.getIndex(res, "id");
	}
	
	Index createBenchmark() {
		return conn.insert("INSERT INTO main_benchmark () VALUES ()");
	}
	
	Index addBenchmarkResult(Index benchmark, Index tool, Index file, int exitCode, std::size_t time) {
		return conn.insert("INSERT INTO main_benchmarkresult (`exitcode`, `time`, `memory`, `benchmark_id`, `tool_id`, `file_id`) VALUES (%0q, %1q, %2q, %3q, %4q, %5q)", exitCode, time, std::size_t(0), benchmark, tool, file);
	}
	
	void addBenchmarkAttribute(Index benchmarkResult, const std::string& key, const std::string& value) {
		conn.insert("INSERT INTO main_benchmarkattribute (`key`, `value`, `result_id`) VALUES (%0q, %1q, %2q)", key, value, benchmarkResult);
	}

	Database() {
		if (!conn.connect("benchmarks", "ths.informatik.rwth-aachen.de", "benchmax", "Km2FLeJJ2wX3nMqq")) {
			BENCHMAX_LOG_FATAL("benchmax.database", "Failed to connect to database.");
			exit(1);
		}
	}
};
#else
class Database {
public:
	typedef std::size_t Index;
	Index addTool(const Tool*) { return 0; }
	Index getToolID(const Tool*) { return 0; }
	Index addFile(const fs::path&) { return 0; }
	Index getFileID(const fs::path&) { return 0; }
	Index createBenchmark() { return 0; }
	Index addBenchmarkResult(Index, Index, Index, int, std::size_t) { return 0; }
	void addBenchmarkAttribute(Index, const std::string&, const std::string&) {}
};
#endif

}
