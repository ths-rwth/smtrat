/**
 * @file Database.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <filesystem>

#ifdef BENCHMAX_DATABASE
// Include exactly one implementation.
#include "Database_mysqlconnector.h"
//#include "Database_mysqlpp.h"
#endif

#include "../logging.h"
#include "../tools/Tool.h"

namespace benchmax {

namespace fs = std::filesystem;

#ifdef BENCHMAX_DATABASE
/**
 * Database abstraction that allows to store benchmark results.
 * Note that it does not abstract from the database (we assume MySQL) but only from the mysql library.
 * 
 * Storing to database should be considered unstable!
 */
class Database {
	DBAL conn;
public:
	/// Index type.
	using Index = DBAL::Index;
	
	/// Add a new tool.
	Index addTool(const Tool* tool) {
		Index id = conn.insert("INSERT INTO main_tool (`interface`, `hash`) VALUES (%0q, %1q)", tool->name(), tool->attributeHash());
		DBAL::Statement stmt = conn.prepare("INSERT INTO main_toolattribute (`key`, `value`, `tool_id`) VALUES (%0q, %1q, %2q)");
		for (const auto& it: tool->attributes()) {
			conn.execute(stmt, it.first, it.second, id);
		}
		return id;
	}

	/// Get id of a tool.
	Index getToolID(const Tool* tool) {
		DBAL::Results res = conn.select("SELECT id FROM main_tool WHERE `interface` = %0q AND `hash` = %1q", tool->name(), tool->attributeHash());
		if (conn.size(res) == 0) {
			return addTool(tool);
		}
		assert(conn.size(res) == 1);
		return conn.getIndex(res, "id");
	}
	
	/// Add a new file.
	Index addFile(const fs::path& file) {
		return conn.insert("INSERT INTO main_file (`filename`) VALUES (%0q)", file.native());
	}
	
	/// Get id of a file.
	Index getFileID(const fs::path& file) {
		DBAL::Results res = conn.select("SELECT id FROM main_file WHERE `filename` = %0q", file.native());
		if (conn.size(res) == 0) {
			return addFile(file);
		}
		assert(conn.size(res) == 1);
		return conn.getIndex(res, "id");
	}
	
	/// Create a new benchmark run.
	Index createBenchmark() {
		return conn.insert("INSERT INTO main_benchmark () VALUES ()");
	}
	
	/// Add results for an individual benchmark.
	Index addBenchmarkResult(Index benchmark, Index tool, Index file, int exitCode, std::size_t time) {
		return conn.insert("INSERT INTO main_benchmarkresult (`exitcode`, `time`, `memory`, `benchmark_id`, `tool_id`, `file_id`) VALUES (%0q, %1q, %2q, %3q, %4q, %5q)", exitCode, time, std::size_t(0), benchmark, tool, file);
	}
	
	/// Add arbitrary attributes for a benchmark result.
	void addBenchmarkAttribute(Index benchmarkResult, const std::string& key, const std::string& value) {
		conn.insert("INSERT INTO main_benchmarkattribute (`key`, `value`, `result_id`) VALUES (%0q, %1q, %2q)", key, value, benchmarkResult);
	}

	/// Establish database connection.
	Database() {
		if (!conn.connect("benchmarks", "ths.informatik.rwth-aachen.de", "benchmax", "Km2FLeJJ2wX3nMqq")) {
			BENCHMAX_LOG_FATAL("benchmax.database", "Failed to connect to database.");
			exit(1);
		}
	}
};
#else
/// Dummy database that effectively disables storing to database. Set BENCHMAX_DATABASE to actually use a database.
class Database {
public:
	/// Dummy index type.
	using Index = std::size_t;
	/// Dummy.
	Index addTool(const Tool*) { return 0; }
	/// Dummy.
	Index getToolID(const Tool*) { return 0; }
	/// Dummy.
	Index addFile(const fs::path&) { return 0; }
	/// Dummy.
	Index getFileID(const fs::path&) { return 0; }
	/// Dummy.
	Index createBenchmark() { return 0; }
	/// Dummy.
	Index addBenchmarkResult(Index, Index, Index, int, std::size_t) { return 0; }
	/// Dummy.
	void addBenchmarkAttribute(Index, const std::string&, const std::string&) {}
};
#endif

}
