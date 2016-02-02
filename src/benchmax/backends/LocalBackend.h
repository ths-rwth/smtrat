/**
 * @file LocalBackend.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <chrono>

#include "Backend.h"

#include "../Settings.h"

#include "../utils/Execute.h"

namespace benchmax {

class LocalBackend: public Backend {
protected:
	virtual void execute(const Tool* tool, const fs::path& file) {
		std::stringstream call;
		call << "ulimit -S -t " << Settings::timeLimit << " && ";
		call << "ulimit -S -v " << (Settings::memoryLimit * 1024) << " && ";
		call << "date +\"Start: %s%3N\" && ";
		call << tool->getCommandline(file.native()) << " 2> stderr.log && ";
		call << "date +\"End: %s%3N\"";
	
		BenchmarkResult results;
		auto start = std::chrono::high_resolution_clock::now();
		
		int exitCode = callProgram(call.str(), results.stdout);
		results.exitCode = WEXITSTATUS(exitCode);
		
		auto end = std::chrono::high_resolution_clock::now();
		results.time = (std::size_t)std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();
	
		tool->additionalResults(file, results);
		
		mResults.addResult(tool, file, results);
	}
};

}
