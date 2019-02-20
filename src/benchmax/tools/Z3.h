#pragma once

#include "Tool.h"

namespace benchmax {

/**
 * Tool wrapper for Z3 for SMT-LIB.
 */
class Z3: public Tool {
public:
	/// New Z3 tool.
	Z3(const fs::path& binary, const std::string& arguments): Tool("Z3", binary, arguments) {
		if (settings_tools().collect_statistics) mArguments += " -st";
	}
	/// Only handle .smt2 files.
	virtual bool canHandle(const fs::path& path) const override {
		return is_extension(path, ".smt2");
	}
	/// Parse answer string from stdout.
	virtual void additionalResults(const fs::path&, BenchmarkResult& result) const override {
		if (result.stdout.find("unsat") != std::string::npos) result.answer = "unsat";
		else if (result.stdout.find("sat") != std::string::npos) result.answer = "sat";
		else if (result.stdout.find("unknown") != std::string::npos) result.answer = "unknown";
		else if (result.stdout.find("out of memory") != std::string::npos) result.answer = "memout";
		else result.answer = "invalid";

		std::regex topRegex("\\(\\s*((?:\\:\\S+\\s*\\S+\\s*)+)\\)");
		std::regex subRegex("\\s*\\:(\\S+)\\s*(\\S+)");
		auto topBegin = std::sregex_iterator(result.stdout.begin(), result.stdout.end(), topRegex);
		auto topEnd = std::sregex_iterator();
		for (auto i = topBegin; i != topEnd; ++i) {
			const std::string& subStdout = (*i)[1];
			auto subBegin = std::sregex_iterator(subStdout.begin(), subStdout.end(), subRegex);
			auto subEnd = std::sregex_iterator();
			for (auto j = subBegin; j != subEnd; ++j) {
				result.additional.emplace((*j)[1], (*j)[2]);
			}
		}
		result.stdout = "";
		result.stderr = "";
	}
};

}
