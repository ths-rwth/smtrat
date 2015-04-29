/**
 * @file Database.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

// Include exactly one implementation.
#include "Database_mysqlconnector.h"
//#include "Database_mysqlpp.h"

#include "../logging.h"

namespace benchmax {

class Database {
	DBAL conn;
public:
	
	typedef DBAL::Index Index;
	
	Index addTool(const Tool& tool) {
		Index id = conn.insert("INSERT INTO tool (interface, hash) VALUES (%0q, %1q)", tool.name(), tool.attributeHash());
		DBAL::Statement stmt = conn.prepare("INSERT INTO toolattributes (toolid, key, value) VALUES (%0q, %1q, %2q)");
		for (const auto& it: tool.attributes()) {
			conn.execute(stmt, id, it.first, it.second);
		}
		return id;
	}
	
	Index getToolID(const Tool& tool) {
		DBAL::Results res = conn.select("SELECT id FROM tool WHERE interface = %0q AND hash = %1q", tool.name(), tool.attributeHash());
		if (conn.size(res) == 0) {
			return addTool(tool);
		}
		assert(conn.size(res) == 1);
		return conn.getIndex(res, "id");
	}
	
	Index addFile(const fs::path& file) {
		return conn.insert("INSERT INTO file (filename) VALUES (%0q)", file.native());
	}
	
	Index getFileID(const fs::path& file) {
		DBAL::Results res = conn.select("SELECT id FROM file WHERE filename = %0q", file.native());
		if (conn.size(res) == 0) {
			return addFile(file);
		}
		assert(conn.size(res) == 1);
		return conn.getIndex(res, "id");
	}
	
	Index createBenchmark() {
		return conn.insert("INSERT INTO benchmark () VALUES ()");
	}
	
	Index addBenchmarkResult(Index benchmark, Index tool, Index file, int exitCode, std::size_t time) {
		return conn.insert("INSERT INTO benchmarkresult (benchmark, tool, file, exitcode, time) VALUES (%0q, %1q, %2q, %3q, %4q)", benchmark, tool, file, exitCode, time);
	}
	
	void addBenchmarkAttribute(Index benchmarkResult, const std::string& key, const std::string& value) {
		conn.insert("INSERT INTO benchmarkattribute (benchmarkresultid, key, value) VALUES (%0q, %1q, %2q)", benchmarkResult, key, value);
	}

	Database() {
		if (!conn.connect("benchmax", "ths.informatik.rwth-aachen.de", "benchmax", "Km2FLeJJ2wX3nMqq")) {
			BENCHMAX_LOG_ERROR("benchmax.database", "Failed to connect to database.");
		}
	}
	
};

}
