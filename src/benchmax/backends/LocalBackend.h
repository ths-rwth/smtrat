/**
 * @file LocalBackend.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <chrono>

#include "Backend.h"

#include "../utils/Execute.h"
#include "../utils/durations.h"

namespace benchmax {

class LocalBackend: public Backend {
protected:
	virtual void execute(const Tool* tool, const fs::path& file, const fs::path& baseDir) {
		std::stringstream call;
		call << "ulimit -S -t " << seconds(settings_benchmarks().limit_time).count() << " && ";
		call << "ulimit -S -v " << (settings_benchmarks().limit_memory * 1024) << " && ";
		call << "date +\"Start: %s%3N\" && ";
		call << tool->getCommandline(file.native()) << " 2> stderr.log && ";
		call << "date +\"End: %s%3N\"";
	
		BenchmarkResult results;
		auto start = std::chrono::high_resolution_clock::now();
		
		int exitCode = callProgram(call.str(), results.stdout);
		results.exitCode = WEXITSTATUS(exitCode);
		
		auto end = std::chrono::high_resolution_clock::now();
		results.time = milliseconds(end - start);
	
		addResult(tool, file, baseDir, results);
	}
};

}
