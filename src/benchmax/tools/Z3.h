/**
 * @file   Z3Tool.h
 *         Created on April 14, 2013, 6:10 PM
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
	std::string getStatus(const BenchmarkResult& result) const override {
		if (result.stdout.find("unsat")) return "unsat";
		if (result.stdout.find("sat")) return "sat";
		if (result.stdout.find("unknown")) return "unknown";
		return "invalid";
	}
};

}
