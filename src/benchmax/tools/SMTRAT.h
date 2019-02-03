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

#include <regex>

namespace benchmax {

class SMTRAT: public Tool {
public:
	SMTRAT(const fs::path& binary, const std::string& arguments): Tool("SMTRAT", binary, arguments) {
		if (settings_tools().collect_statistics) mArguments += " --stats:print";
	}

	virtual bool canHandle(const fs::path& path) const override {
		return isExtension(path, ".smt2");
	}
	
	std::string getStatusFromOutput(const BenchmarkResult& result) const {
		if (result.stderr.find("GNU MP: Cannot allocate memory") != std::string::npos) return "memout";
		if (result.stderr.find("Minisat::OutOfMemoryException") != std::string::npos) return "memout";
		return "segfault";
	}
	
	std::map<std::string,std::string> parseOptions(const std::string& options) const {
		std::map<std::string,std::string> res;
		std::regex r("^(.+) = (.+)\n");
		auto begin = std::sregex_iterator(options.begin(), options.end(), r);
		auto end = std::sregex_iterator();
		for (auto i = begin; i != end; ++i) {
			res[(*i)[1]] = (*i)[2];
		}
		return res;
	}
	
	virtual void additionalResults(const fs::path&, BenchmarkResult& result) const override {
		switch (result.exitCode) {
			case 2: result.answer = "sat"; break;
			case 3: result.answer = "unsat"; break;
			case 4: result.answer = "unknown"; break;
			case 5: result.answer = "wrong"; break;
			case 9: result.answer = "nosuchfile"; break;
			case 10: result.answer = "parsererror"; break;
			case 11: result.answer = "timeout"; break;
			case 12: result.answer = "memout"; break;
			default: result.answer = getStatusFromOutput(result);
		}
		std::regex topRegex("\\(\\:(\\S+)\\s*\\(\\s*((?:\\:\\S+\\s*\\S+\\s*)+)\\)\\)");
		std::regex subRegex("\\s*\\:(\\S+)\\s*(\\S+)");

		auto topBegin = std::sregex_iterator(result.stdout.begin(), result.stdout.end(), topRegex);
		auto topEnd = std::sregex_iterator();
		for (auto i = topBegin; i != topEnd; ++i) {
			const std::string& prefix = (*i)[1];
			const std::string& subStdout = (*i)[2];

			auto subBegin = std::sregex_iterator(subStdout.begin(), subStdout.end(), subRegex);
			auto subEnd = std::sregex_iterator();
			for (auto j = subBegin; j != subEnd; ++j) {
				std::string name = prefix + "_" + std::string((*j)[1]);
				result.additional.emplace(name, (*j)[2]);
			}
		}
		result.stdout = "";
		result.stderr = "";
	}
};

}
