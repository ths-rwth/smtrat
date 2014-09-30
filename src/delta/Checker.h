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

namespace delta {

/**
 * This class takes care of calling the actual solver.
 */
class Checker {
	/// Solver executable filename.
	std::string executable;
	/// Timeout for a single call.
	unsigned timeout;
	/// Filename of the temporary file.
	std::string temp;
	/// Expected exit code.
	int expected;

	/**
	 * Execute the solver on the given filename and return the exit code.
	 * @param filename Input filename.
	 * @return Exit code.
	 */
	int execute(const std::string& filename) {
		std::stringstream ss;
		ss << "sh -c \"";
		ss << "ulimit -t " << timeout << ";";
		ss << executable << " " << filename << " 2> /dev/null > /dev/null";
		ss << "\" 2> /dev/null";
		int code = system(ss.str().c_str());
		return WEXITSTATUS(code);
	}
public:
	/**
	 * Creates a new checker.
	 * @param exec Filename of the solver executable.
	 * @param temp Filename of the temporary file.
	 * @param timeout Timeout for a single call to the solver.
	 * @param original Filename of the original file to obtain the expected exit code.
	 */
	Checker(const std::string& exec, const std::string& temp, unsigned timeout, const std::string& original):
		executable(exec), timeout(timeout), temp(temp), expected(execute(original))
	{
		std::cout << "Expected exit code: " << expected << std::endl;
	}

	/**
	 * Call the solver with the given node.
	 * Checks if the exit code is the same as for the original file.
	 * @param n Input data.
	 * @return If the exit code is still the same.
	 */
	bool operator()(const Node& n) {
		std::fstream out(temp, std::ios::out);
		out << n;
		out.close();
		return execute(temp) == expected;
	}
};

}