/**
 * @file LocalBackend.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <chrono>

#include "Backend.h"
#include "local/LocalSettings.h"

#include "../utils/execute.h"

namespace benchmax {

/**
 * This backend simply runs files sequentially on the local machine.
 */
class LocalBackend: public Backend {
protected:
	/// Execute the tool on the file manually.
	virtual void execute(const Tool* tool, const fs::path& file) {
		std::stringstream call;
		call << "ulimit -S -t " << std::chrono::seconds(settings_benchmarks().limit_time).count() << " && ";
		call << "ulimit -S -v " << settings_benchmarks().limit_memory.kibi() << " && ";
		call << "date +\"Start: %s%3N\" && ";
		if (settings_local().measure_peak_memory) {
			call << "/usr/bin/time -v ";
		}
		call << tool->getCommandline(file.native()) << " 2> stderr.log && ";
		call << "date +\"End: %s%3N\"";
	
		BenchmarkResult results;
		auto start = std::chrono::high_resolution_clock::now();
		
		int exitCode = call_program(call.str(), results.stdout);
		results.exitCode = WEXITSTATUS(exitCode);
		
		auto end = std::chrono::high_resolution_clock::now();
		results.time = std::chrono::duration_cast<decltype(results.time)>(end - start);

		std::ifstream ifs("stderr.log");
		results.stderr.assign((std::istreambuf_iterator<char>(ifs)), (std::istreambuf_iterator<char>()));
		if (settings_local().measure_peak_memory) {
			std::regex regexpr("Maximum resident set size \\(kbytes\\): ([0-9]+)");
			std::smatch base_match;
			bool match = std::regex_search(results.stderr, base_match, regexpr);
			assert(match && base_match.size() == 2);
			std::ssub_match base_sub_match = base_match[1];
			results.additional.emplace("memory", base_sub_match.str());
		}
		results.stderr.clear();
	
		addResult(tool, file, std::move(results));
		madeProgress();
	}
};

}
