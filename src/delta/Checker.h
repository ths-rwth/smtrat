/**
 * @file Checker.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <cstdlib>
#include <cstdio>

#include <fstream>
#include <sstream>

#include "operators.h"
#include "../cli/config.h"

namespace delta {

/**
 * This class takes care of calling the actual solver.
 */
class Checker {
	/// Solver executable filename.
	std::string executable;
	/// Memout for a single call.
	std::size_t memout;
	/// Timeout for a single call.
	std::size_t timeout;
	/// Expected exit code.
	int expected;
	/// Flag is some process has been killed.
	mutable std::atomic<std::size_t> killed;

	/**
	 * Execute the solver on the given filename and return the exit code.
	 * @param filename Input filename.
	 * @return Exit code.
	 */
	int execute(const std::string& filename) const {
#ifdef __WIN
        //TODO do something!
        assert(false);
        return -1;
#else
		std::stringstream ss;
		ss << "sh -c \"";
		ss << "ulimit -t " << timeout << ";";
		ss << "ulimit -S -v " << memout*1024 << " ;";
		ss << executable << " " << filename << " 2> /dev/null > /dev/null";
		ss << "\" 2> /dev/null";
		int code = system(ss.str().c_str());
		int exitcode = WEXITSTATUS(code);
		if (exitcode > 128) killed++;
		return exitcode;
#endif
	}
public:
	/**
	 * Creates a new checker.
	 * @param exec Filename of the solver executable.
	 * @param timeout Timeout for a single call to the solver.
	 * @param original Filename of the original file to obtain the expected exit code.
	 */
	Checker(const std::string& exec, std::size_t memout, std::size_t timeout, const std::string& original):
		executable(exec), memout(memout), timeout(timeout), expected(execute(original)), killed(0)
	{}

	/**
	 * Call the solver with the given node.
	 * Checks if the exit code is the same as for the original file.
	 * @param n Input data.
	 * @param temp Filename of the temporary file.
	 * @return If the exit code is still the same.
	 */
	bool operator()(const Node& n, const std::string& temp) const {
		std::fstream out(temp, std::ios::out);
		out << n;
		out.close();
		return execute(temp) == expected;
	}
	/**
	 * Return expected exit code.
     * @return Expected exit code.
     */
	int expectedCode() const {
		return expected;
	}
	
	std::size_t getKilled() const {
		return killed;
	}
	void resetKilled() const {
		killed = 0;
	}
	void resetTimeout(std::size_t t) {
		timeout = t;
	}
};

}
