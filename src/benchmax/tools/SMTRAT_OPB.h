/**
 * @file   smtratSolverTool.h
 * @author: Sebastian Junges
 *
 *
 */

#pragma once

#include "Tool.h"

#include "../utils/Execute.h"
#include "../utils/regex.h"
#include "../utils/strings.h"

namespace benchmax {

class SMTRAT_OPB: public Tool {
public:
	SMTRAT_OPB(const fs::path& binary, const std::string& arguments): Tool("SMTRAT-OPB", binary, arguments) {
		if (settings_tools().collect_statistics) mArguments += " -s";
		mArguments += " -opb";
	}

	virtual bool canHandle(const fs::path& path) const override {
		return isExtension(path, ".opb");
	}
	
	std::string getStatusFromOutput(const BenchmarkResult& result) const {
		if (result.stderr.find("GNU MP: Cannot allocate memory") != std::string::npos) return "memout";
		if (result.stderr.find("Minisat::OutOfMemoryException") != std::string::npos) return "memout";
		return "segfault";
	}
	
	std::map<std::string,std::string> parseOptions(const std::string& options) const {
		std::map<std::string,std::string> res;
		regex r("^(.+) = (.+)\n");
		auto begin = sregex_iterator(options.begin(), options.end(), r);
		auto end = sregex_iterator();
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
		
		regex topRegex("\\(\\:(\\S+)\\s*\\(((?:\\:\\S+\\s*\\S+\\s*)+)\\)\\)");
		regex subRegex("\\s*\\:(\\S+)\\s*(\\S+)");

		auto topBegin = sregex_iterator(result.stdout.begin(), result.stdout.end(), topRegex);
		auto topEnd = sregex_iterator();
		for (auto i = topBegin; i != topEnd; ++i) {
			const std::string& prefix = (*i)[1];
			const std::string& subStdout = (*i)[2];

			auto subBegin = sregex_iterator(subStdout.begin(), subStdout.end(), subRegex);
			auto subEnd = sregex_iterator();
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
