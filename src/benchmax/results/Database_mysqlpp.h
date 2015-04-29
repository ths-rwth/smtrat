/**
 * @file Database_mysqlpp.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#define MYSQLPP_MYSQL_HEADERS_BURIED
#include <mysql++/mysql++.h>
#include <mysql++/sql_types.h>

#include "../logging.h"

namespace benchmax {

class DBAL {
	mysqlpp::Connection conn;
public:
	typedef mysqlpp::sql_bigint_unsigned Index;
	typedef mysqlpp::Query Statement;
	typedef mysqlpp::StoreQueryResult Results;
	
	bool connect(const std::string& db, const std::string& host, const std::string& user, const std::string& password) {
		return conn.connect(db.c_str(), host.c_str(), user.c_str(), password.c_str());
	}
	Statement prepare(const std::string& query) {
		Statement s = conn.query(query);
		s.parse();
		return s;
	}
	template<typename... Args>
	void execute(Statement& stmt, const Args&... args) {
		stmt.execute(args...);
	}
	template<typename... Args>
	Index insert(const std::string& query, const Args&... args) {
		Statement s = prepare(query);
		mysqlpp::SimpleResult res = s.execute(args...);
		return res.insert_id();
	}
	template<typename... Args>
	Results select(const std::string& query, const Args&... args) {
		Statement s = prepare(query);
		return s.store(args...);
	}
	std::size_t size(const Results& res) {
		return res.size();
	}
	Index getIndex(const Results& res, const std::string& name) {
		return res[0][name.c_str()];
	}
};

}
