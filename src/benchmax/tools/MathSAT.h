#pragma once

#include "Tool.h"

#include <regex>

namespace benchmax {

/**
 * Tool wrapper for MathSAT for SMT-LIB.
 */
class MathSAT: public Tool {
public:
	/// New MathSAT tool.
	MathSAT(const fs::path& binary, const std::string& arguments): Tool("MathSAT", binary, arguments) {
		mArguments += " -input=smt2 <";
	}

	/// Only handle .smt2 files.
	virtual bool canHandle(const fs::path& path) const override {
		return is_extension(path, ".smt2");
	}
	
	/// Computes the answer string from the exit code and parses statistics output.
	virtual void additionalResults(const fs::path&, BenchmarkResult& result) const override {
		if (result.stdout.find("unsat") != std::string::npos) result.answer = "unsat";
		else if (result.stdout.find("sat") != std::string::npos) result.answer = "sat";
		else if (result.stdout.find("unknown") != std::string::npos) result.answer = "unknown";
		else if (result.stdout.find("out of memory") != std::string::npos) result.answer = "memout";
		else result.answer = "invalid";
		
		result.stdout = "";
		result.stderr = "";
	}
};

}
