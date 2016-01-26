/**
 * @file   smtratSolverTool.h
 *         Created on April 10, 2013, 3:37 PM
 * @author: Sebastian Junges
 *
 *
 */

#pragma once

#include "Tool.h"

#include "../utils/Execute.h"
#include "../utils/regex.h"

namespace benchmax {

class SMTRAT: public Tool {
public:
	SMTRAT(const fs::path& binary, const std::string& arguments): Tool("SMTRAT", binary, arguments) {}

	virtual bool canHandle(const fs::path& path) const override {
		return isExtension(path, ".smt2");
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
	
	virtual void additionalResults(const fs::path&, BenchmarkResult& results) const override {
		regex topRegex("\\(\\:(\\S+)\\s*\\(((?:\\:\\S+\\s*\\S+\\s*)+)\\)\\)");
		regex subRegex("\\s*\\:(\\S+)\\s*(\\S+)");

		auto topBegin = sregex_iterator(results.stdout.begin(), results.stdout.end(), topRegex);
		auto topEnd = sregex_iterator();
		for (auto i = topBegin; i != topEnd; ++i) {
			const std::string& prefix = (*i)[1];
			const std::string& subStdout = (*i)[2];

			auto subBegin = sregex_iterator(subStdout.begin(), subStdout.end(), subRegex);
			auto subEnd = sregex_iterator();
			for (auto j = subBegin; j != subEnd; ++j) {
				std::string name = prefix + "_" + std::string((*j)[1]);
				results.additional.emplace(name, (*j)[2]);
			}
		}
	}
};

}
