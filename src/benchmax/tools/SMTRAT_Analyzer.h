#pragma once

#include "Tool.h"

#include <regex>

namespace benchmax {

/**
 * Tool wrapper for SMT-RAT for SMT-LIB.
 */
class SMTRAT_Analyzer: public Tool {
public:
	/// New SMT-RAT tool.
	SMTRAT_Analyzer(const fs::path& binary, const std::string& arguments): Tool("SMTRAT_Analyzer", binary, arguments) {
		mArguments += " --stats.print --analyze.enabled";
	}

	/// Only handle .smt2 files.
	virtual bool canHandle(const fs::path& path) const override {
		return is_extension(path, ".smt2");
	}
		
	/// Computes the answer string from the exit code and parses statistics output.
	virtual void additionalResults(const fs::path&, BenchmarkResult& result) const override {
		result.answer = "sat";

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
