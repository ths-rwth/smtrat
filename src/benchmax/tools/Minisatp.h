/**
 * @file   smtratSolverTool.h
 * @author: Sebastian Junges
 *
 *
 */

#pragma once

#include "Tool.h"

#include "../utils/Execute.h"
#include "../utils/strings.h"

namespace benchmax {

class Minisatp: public Tool {
public:
	Minisatp(const fs::path& binary, const std::string& arguments): Tool("Minisatp", binary, arguments) {
		mArguments += " -v0";
	}

	virtual bool canHandle(const fs::path& path) const override {
		return isExtension(path, ".opb");
	}
	
	virtual void additionalResults(const fs::path&, BenchmarkResult& result) const override {
		if (result.stdout.find("s OPTIMUM FOUND") != std::string::npos) result.answer = "sat";
		else if (result.stdout.find("s SATISFIABLE") != std::string::npos) result.answer = "sat";
		else if (result.stdout.find("s UNSATISFIABLE") != std::string::npos) result.answer = "unsat";
		else if (result.stdout.find("s UNKNOWN") != std::string::npos) result.answer = "unknown";
		else result.answer = "timeout";
	}
};

}
