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
 * Tool wrapper for a Minisat solver.
 */
class Minisat: public Tool {
public:
	/// Create tool.
	Minisat(const fs::path& binary, const std::string& arguments): Tool("Minisat", binary, arguments) {}

	/// Only handles .opb files.
	virtual bool canHandle(const fs::path& path) const override {
		return is_extension(path, ".cnf") || is_extension(path, ".dimacs");
	}
	
	/// Parse results from stdout.
	virtual void additionalResults(const fs::path&, BenchmarkResult& result) const override {
		if (result.exitCode == 10) result.answer = "sat";
		else if (result.exitCode == 20) result.answer = "unsat";
		else result.answer = "unknown";
	}
};

}
