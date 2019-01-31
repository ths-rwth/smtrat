/**
 * @file CondorBackend.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <atomic>
#include <cstdlib>
#include <fstream>
#include <future>

#include "Backend.h"

#include "../logging.h"
#include "../settings/Settings.h"
#include "../utils/durations.h"

namespace benchmax {

class CondorBackend: public Backend {
protected:
	virtual void execute(const Tool*, const fs::path&, const fs::path&) {}
private:
	std::list<std::atomic<bool>> processes;

	std::string generateSubmitFile(std::size_t ID, const Tool& tool, const BenchmarkSet& b) {
		std::ofstream wrapper(".wrapper_" + std::to_string(ID));
		wrapper << "#!/bin/sh" << std::endl;
		wrapper << "ulimit -S -t " << seconds(settings_benchmarks().limit_time).count() << std::endl;
		wrapper << "ulimit -S -v " << (settings_benchmarks().limit_memory * 1024) << std::endl;
		wrapper << "date +\"Start: %s%3N\"" << std::endl;
		wrapper << tool.getCommandline("$*") << std::endl;
		wrapper << "date +\"End: %s%3N\"" << std::endl;
		wrapper.close();

		std::ofstream out(".jobs." + std::to_string(ID));
		out << "executable = .wrapper_" << ID << std::endl;
		out << "output = out/out." << ID << ".$(cluster).$(process)" << std::endl;
		out << "error = out/err." << ID << ".$(cluster).$(process)" << std::endl;
		out << "log = out/log." << ID << std::endl;
		out << "periodic_hold = (time() - JobCurrentStartExecutingDate) > " << seconds(settings_benchmarks().limit_time).count() << std::endl;
		
		for (const auto& file: b) {
			if (!tool.canHandle(file)) continue;
			out << "transfer_input_files = " << file.native() << ", " << tool.binary().native() << std::endl;
			out << "arguments = " << file.filename().native() << std::endl;
			out << "queue" << std::endl;
		}
		out.close();
		return ".jobs." + std::to_string(ID);
	}
	
	void collectResults(std::size_t ID) {
		typedef fs::directory_iterator dirIt;
		
		for (dirIt it("out/"), end; it != end; ++it) {
			std::string name = it->path().native();
			if (name.find("out/out." + std::to_string(ID)) != std::string::npos) {
				
			}
		}
	}
	
	void runAndWait(std::size_t ID, const std::string& submitFile, std::atomic<bool>& it) {
		BENCHMAX_LOG_INFO("benchmax.condor", "Queueing batch " << ID << "...");
		std::system(("condor_submit " + submitFile).c_str());
		BENCHMAX_LOG_INFO("benchmax.condor", "Waiting for batch " << ID << "...");
		std::system(("condor_wait out/log." + std::to_string(ID)).c_str());
		BENCHMAX_LOG_INFO("benchmax.condor", "Collecting statistics for batch " << ID << "...");
		collectResults(ID);
		BENCHMAX_LOG_INFO("benchmax.condor", "Finished batch " << ID << ".");
		it = true;
	}
	
public:
	void run(const Tools& tools, const std::vector<BenchmarkSet>& benchmarks) {
		BENCHMAX_LOG_INFO("benchmax.condor", "Generating submit files...");
		
		for (const auto& tool: tools) {
			for (const BenchmarkSet& set: benchmarks) {
				std::size_t ID = processes.size() + 1;
				std::string submitFile = generateSubmitFile(ID, *tool.get(), set);
				processes.emplace_back(false);
				std::async(&CondorBackend::runAndWait, this, ID, std::ref(submitFile), std::ref(processes.back()));
			}
		}
		while (!processes.empty()) {
			while (!processes.front()) usleep(1000000);
			assert(processes.front());
			processes.pop_front();
		}
	}
};

}
