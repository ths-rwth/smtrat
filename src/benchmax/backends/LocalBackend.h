/**
 * @file LocalBackend.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <chrono>

#include "Backend.h"
#include "BackendData.h"

#include "../Settings.h"

namespace benchmax {

class LocalBackend: public Backend {
protected:
	virtual void execute(const Tool& tool, const fs::path& file) {
		std::stringstream call;
		call << "ulimit -S -t " << Settings::timeLimit << " && ";
		call << "ulimit -S -v " << (Settings::memoryLimit * 1024) << " && ";
		call << "date +\"Start: %s%3N\" && ";
		call << tool.getCommandline(file) << " 2> stderr.log && ";
		call << "date +\"End: %s%3N\"";
	
		BenchmarkResults results;
		auto start = std::chrono::high_resolution_clock::now();
		
		FILE* pipe = popen(call.str().c_str(), "r");
		char buf[255];
		while (!feof(pipe)) {
			if (fgets(buf, sizeof(buf), pipe) != nullptr) {
				results.stdout += buf;
			}
		}
		int exitCode = pclose(pipe);
		results.exitCode = WEXITSTATUS(exitCode);
		
		auto end = std::chrono::high_resolution_clock::now();
		results.time = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();
		
		mResults.addResult(tool, file, results);
	}
public:
	/*void run() {
		for (const auto& benchmark: data->benchmarks)
		{
			benchmark->printSettings();
			benchmark->run();
			BENCHMAX_LOG_DEBUG("benchmax", "Benchmark " << benchmark->benchmarkName() << " done!");
			benchmark->printResults();
			if(benchmark->produceLaTeX())
			{
				std::string benchmarkString = benchmark->benchmarkName() + " (" + boost::lexical_cast<string>(benchmark->benchmarkCount()) + ")";
				data->table[pair<string, string>(benchmarkString, benchmark->solverName())] = benchmark;
				data->benchmarkSet.insert(benchmarkString);
				data->solverSet.insert(benchmark->solverName());
			}
		}

		if(Settings::ValidationTool != nullptr)
		{
			std::string wrongResultPath = Settings::WrongResultPath.substr(0, Settings::WrongResultPath.size() - 1);
			fs::path path(wrongResultPath);
			if(fs::exists(path))
			{
				std::string tarCall = std::string("tar zcfP " + wrongResultPath + ".tgz " + wrongResultPath);
				system(tarCall.c_str());
				fs::remove_all(fs::path(Settings::WrongResultPath));
			}
		}
	}*/
};

}
