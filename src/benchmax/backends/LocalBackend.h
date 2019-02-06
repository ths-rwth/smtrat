/**
 * @file LocalBackend.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <chrono>

#include "Backend.h"

#include "../utils/Execute.h"

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
		call << "ulimit -S -v " << (settings_benchmarks().limit_memory * 1024) << " && ";
		call << "date +\"Start: %s%3N\" && ";
		call << tool->getCommandline(file.native()) << " 2> stderr.log && ";
		call << "date +\"End: %s%3N\"";
	
		BenchmarkResult results;
		auto start = std::chrono::high_resolution_clock::now();
		
		int exitCode = call_program(call.str(), results.stdout);
		results.exitCode = WEXITSTATUS(exitCode);
		
		auto end = std::chrono::high_resolution_clock::now();
		results.time = std::chrono::duration_cast<decltype(results.time)>(end - start);
	
		addResult(tool, file, results);
	}
};

}
