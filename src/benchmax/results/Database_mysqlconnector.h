/**
 * @file Database_mysqlconnector.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <mysql_connection.h>
#include <cppconn/driver.h>
#include <cppconn/resultset.h>
#include <cppconn/prepared_statement.h>

#include "../logging.h"

namespace benchmax {
	
class DBAL {
	sql::Driver* driver;
	sql::Connection* conn;
	std::string replacePlaceholders(const std::string& s) {
		std::string res = s;
		for (std::size_t i = 0; i < 10; i++) {
			std::string pat = "%" + std::to_string(i) + "q";
			while (true) {
				std::size_t p = res.find(pat);
				if (p == std::string::npos) break;
				res = res.replace(p, pat.size(), "?");
			}
		}
		return res;
	}
public:
	typedef std::size_t Index;
	typedef std::unique_ptr<sql::PreparedStatement> Statement;
	typedef std::unique_ptr<sql::ResultSet> Results;
	
	DBAL(): driver(nullptr), conn(nullptr) {
	}
	~DBAL() {
		delete conn;
	}
	
	bool connect(const std::string& db, const std::string& host, const std::string& user, const std::string& password) {
		try {
			driver = get_driver_instance();
			conn = driver->connect("tcp://" + host + ":3306", user, password);
			conn->setSchema(db);
			return true;
		} catch (sql::SQLException &e) {
			return false;
		}
	}
	Statement prepare(const std::string& query) {
		return Statement(conn->prepareStatement(replacePlaceholders(query)));
	}
	Results execute(Statement& stmt) {
		return Results(stmt->executeQuery());
	}
	Results execute(Statement& stmt, const std::string& a1) {
		stmt->setString(1, a1);
		return Results(stmt->executeQuery());
	}
	Results execute(Statement& stmt, const std::string& a1, std::size_t a2) {
		stmt->setString(1, a1);
		stmt->setUInt64(2, a2);
		return Results(stmt->executeQuery());
	}
	Results execute(Statement& stmt, const Index& a1, const std::string& a2, const std::string& a3) {
		stmt->setUInt64(1, a1);
		stmt->setString(2, a2);
		stmt->setString(3, a3);
		return Results(stmt->executeQuery());
	}
	Results execute(Statement& stmt, const Index& a1, const Index& a2, const Index& a3, int a4, std::size_t a5) {
		stmt->setUInt64(1, a1);
		stmt->setUInt64(2, a2);
		stmt->setUInt64(3, a3);
		stmt->setInt(4, a4);
		stmt->setUInt64(5, a5);
		return Results(stmt->executeQuery());
	}
	template<typename... Args>
	Index insert(const std::string& query, const Args&... args) {
		Statement s = prepare(query);
		execute(s, args...);
		
		std::unique_ptr<sql::Statement> stmt(conn->createStatement());
		Results res(stmt->executeQuery("SELECT @@identity AS id"));
		res->next(); 
		return res->getUInt64("id"); 
	}
	template<typename... Args>
	Results select(const std::string& query, const Args&... args) {
		Statement s = prepare(query);
		return execute(s, args...);
	}
	std::size_t size(const Results& res) {
		return res->rowsCount();
	}
	Index getIndex(const Results& res, const std::string& name) {
		res->next();
		return res->getUInt64(name.c_str());
	}
};

}
