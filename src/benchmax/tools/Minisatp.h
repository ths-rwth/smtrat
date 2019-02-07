/**
 * @file   smtratSolverTool.h
 * @author: Sebastian Junges
 *
 *
 */

#pragma once

#include "Tool.h"

namespace benchmax {

/**
 * Tool wrapper for the Minisatp solver for pseudo-Boolean problems.
 */
class Minisatp: public Tool {
public:
	/// Create tool, add "-v0" to arguments.
	Minisatp(const fs::path& binary, const std::string& arguments): Tool("Minisatp", binary, arguments) {
		mArguments += " -v0";
	}

	/// Only handles .opb files.
	virtual bool canHandle(const fs::path& path) const override {
		return is_extension(path, ".opb");
	}
	
	/// Parse results from stdout.
	virtual void additionalResults(const fs::path&, BenchmarkResult& result) const override {
		if (result.stdout.find("s OPTIMUM FOUND") != std::string::npos) result.answer = "sat";
		else if (result.stdout.find("s SATISFIABLE") != std::string::npos) result.answer = "sat";
		else if (result.stdout.find("s UNSATISFIABLE") != std::string::npos) result.answer = "unsat";
		else if (result.stdout.find("s UNKNOWN") != std::string::npos) result.answer = "unknown";
		else result.answer = "timeout";
	}
};

}
