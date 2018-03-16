/**
 * @file   smtratSolverTool.h
 *         Created on April 10, 2013, 3:37 PM
 * @author: Sebastian Junges
 *
 *
 */

#pragma once

#include "Tool.h"

#include "../Settings.h"
#include "../utils/Execute.h"
#include "../utils/regex.h"

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
		if (result.stdout.find("s OPTIMUM FOUND") != std::string::npos) result.additional["answer"] = "sat";
		else if (result.stdout.find("s SATISFIABLE") != std::string::npos) result.additional["answer"] = "sat";
		else if (result.stdout.find("s UNSATISFIABLE") != std::string::npos) result.additional["answer"] = "unsat";
		else if (result.stdout.find("s UNKNOWN") != std::string::npos) result.additional["answer"] = "unknown";
		else result.additional["answer"] = "timeout";
	}
};

}
