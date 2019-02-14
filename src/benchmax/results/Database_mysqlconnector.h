/**
 * @file Database_mysqlconnector.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <mysql_connection.h>
#include <cppconn/driver.h>
#include <cppconn/exception.h>
#include <cppconn/resultset.h>
#include <cppconn/prepared_statement.h>

#include "../logging.h"

namespace benchmax {
	
class DBAL {
	std::unique_ptr<sql::Driver> driver;
	std::unique_ptr<sql::Connection> conn;
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
	/// Indec type.
	using Index = std::size_t;
	/// Statement type.
	using Statement = std::unique_ptr<sql::PreparedStatement>;
	/// Results type.
	using Results = std::unique_ptr<sql::ResultSet>;
	
	/// Connect to the given database.
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
	/// Prepare a statement.
	Statement prepare(const std::string& query) {
		return Statement(conn->prepareStatement(replacePlaceholders(query)));
	}
	/// Execute a statement without arguments.
	Results execute(Statement& stmt) {
		return Results(stmt->executeQuery());
	}
	/// Execute a statement with a single string.
	Results execute(Statement& stmt, const std::string& a1) {
		stmt->setString(1, a1);
		return Results(stmt->executeQuery());
	}
	/// Execute a statement with a string and a number.
	Results execute(Statement& stmt, const std::string& a1, std::size_t a2) {
		stmt->setString(1, a1);
		stmt->setUInt64(2, a2);
		return Results(stmt->executeQuery());
	}
	/// Execute a statement with two strings and an index.
	Results execute(Statement& stmt, const std::string& a1, const std::string& a2, const Index& a3) {
		stmt->setString(1, a1);
		stmt->setString(2, a2);
		stmt->setUInt64(3, a3);
		return Results(stmt->executeQuery());
	}
	/// Execute a statement with an int, two numbers and three indices.
	Results execute(Statement& stmt, int a1, std::size_t a2, std::size_t a3, const Index& a4, const Index& a5, const Index& a6) {
		stmt->setInt(1, a1);
		stmt->setUInt64(2, a2);
		stmt->setUInt64(3, a3);
		stmt->setUInt64(4, a4);
		stmt->setUInt64(5, a5);
		stmt->setUInt64(6, a6);
		return Results(stmt->executeQuery());
	}
	/// Insert some data and return the new index.
	template<typename... Args>
	Index insert(const std::string& query, const Args&... args) {
		Statement s = prepare(query);
		execute(s, args...);
		
		std::unique_ptr<sql::Statement> stmt(conn->createStatement());
		Results res(stmt->executeQuery("SELECT @@identity AS id"));
		res->next(); 
		return res->getUInt64("id"); 
	}
	/// Select some data.
	template<typename... Args>
	Results select(const std::string& query, const Args&... args) {
		Statement s = prepare(query);
		return execute(s, args...);
	}
	/// Return the size of the results.
	std::size_t size(const Results& res) {
		return res->rowsCount();
	}
	/// Get the index of some name within the results.
	Index getIndex(const Results& res, const std::string& name) {
		res->next();
		return res->getUInt64(name.c_str());
	}
};

}
