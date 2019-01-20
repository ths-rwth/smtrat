/**
 * @file   Z3Tool.h
 * @author: Sebastian Junges
 *
 *
 */

#pragma once

#include "Tool.h"

namespace benchmax {

class Z3: public Tool {
public:
	Z3(const fs::path& binary, const std::string& arguments): Tool("Z3", binary, arguments) {}
	virtual bool canHandle(const fs::path& path) const override {
		return isExtension(path, ".smt2");
	}
	virtual void additionalResults(const fs::path&, BenchmarkResult& result) const override {
		if (result.stdout.find("unsat") != std::string::npos) result.answer = "unsat";
		else if (result.stdout.find("sat") != std::string::npos) result.answer = "sat";
		else if (result.stdout.find("unknown") != std::string::npos) result.answer = "unknown";
		else if (result.stdout.find("out of memory") != std::string::npos) result.answer = "memout";
		else result.answer = "invalid";
	}
};

}
