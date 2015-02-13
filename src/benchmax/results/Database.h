/**
 * @file Database.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#define MYSQLPP_MYSQL_HEADERS_BURIED
#include <mysql++/mysql++.h>
#include <mysql++/sql_types.h>

#include "../logging.h"

namespace benchmax {

class Database {
	
	mysqlpp::Connection conn;
public:
	
	typedef mysqlpp::sql_bigint_unsigned Index;
	
	Index addTool(const Tool& tool) {
		mysqlpp::Query q = conn.query("INSERT INTO tool (interface, hash) VALUES (%0q, %1q)");
		q.parse();
		mysqlpp::SimpleResult res = q.execute(tool.name(), tool.attributeHash());
		std::cout << res.info() << std::endl;
		mysqlpp::Query attrq = conn.query("INSERT INTO toolattributes (toolid, key, value) VALUES (%0q, %1q, %2q)");
		attrq.parse();
		for (const auto& it: tool.attributes()) {
			attrq.execute(res.insert_id(), it.first, it.second);
		}
		return res.insert_id();
	}
	
	Index getToolID(const Tool& tool) {
		std::size_t hash = tool.attributeHash();
		mysqlpp::Query q = conn.query("SELECT id FROM tool WHERE interface = %0q AND hash = %1q");
		q.parse();
		mysqlpp::StoreQueryResult results = q.store(tool.name(), hash);
		if (results.size() == 0) {
			return addTool(tool);
		}
		assert(results.size() == 1);
		return results[0]["id"];
	}
	
	Index addFile(const fs::path& file) {
		mysqlpp::Query q = conn.query("INSERT INTO file (filename) VALUES (%0q)");
		q.parse();
		mysqlpp::SimpleResult res = q.execute(file.native());
		return res.insert_id();
	}
	
	Index getFileID(const fs::path& file) {
		mysqlpp::Query q = conn.query("SELECT id FROM file WHERE filename = %0q");
		q.parse();
		mysqlpp::StoreQueryResult results = q.store(file.native());
		if (results.size() == 0) {
			return addFile(file);
		}
		assert(results.size() == 1);
		return results[0]["id"];
	}
	
	Index createBenchmark() {
		mysqlpp::Query q = conn.query("INSERT INTO benchmark () VALUES ()");
		mysqlpp::SimpleResult res = q.execute();
		return res.insert_id();
	}
	
	Index addBenchmarkResult(Index benchmark, Index tool, Index file, int exitCode, std::size_t time) {
		mysqlpp::Query q = conn.query("INSERT INTO benchmarkresult (benchmark, tool, file, exitcode, time) VALUES (%0q, %1q, %2q, %3q, %4q)");
		q.parse();
		mysqlpp::SimpleResult res = q.execute(benchmark, tool, file, exitCode, time);
		return res.insert_id();
	}
	
	void addBenchmarkAttribute(Index benchmarkResult, const std::string& key, const std::string& value) {
		mysqlpp::Query q = conn.query("INSERT INTO benchmarkattribute (benchmarkresultid, key, value) VALUES (%0q, %1q, %2q)");
		q.parse();
		q.execute(benchmarkResult, key, value);
	}

	Database(): conn(true) {
		if (!conn.connect("benchmax", "ths.informatik.rwth-aachen.de", "benchmax", "Km2FLeJJ2wX3nMqq")) {
			BENCHMAX_LOG_ERROR("benchmax.database", "Failed to connect to database.");
		}
	}
	
};

}