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

namespace benchmax {

/**
 * Backend for the HTCondor batch system.
 * Currently submits all jobs individually and asynchronously waits for them to finish.
 */
class CondorBackend: public Backend {
protected:
	/// No-op version of execute.
	virtual void execute(const Tool*, const fs::path&) {}
private:
	/// List of processes that are currently running.
	std::list<std::atomic<bool>> processes;

	/// Generate a submit file for the given job.
	std::string generateSubmitFile(std::size_t ID, const Tool& tool, const BenchmarkSet& b) {
		std::ofstream wrapper(".wrapper_" + std::to_string(ID));
		wrapper << "#!/bin/sh" << std::endl;
		wrapper << "ulimit -S -t " << std::chrono::seconds(settings_benchmarks().limit_time).count() << std::endl;
		wrapper << "ulimit -S -v " << settings_benchmarks().limit_memory.kibi() << std::endl;
		wrapper << "date +\"Start: %s%3N\"" << std::endl;
		wrapper << tool.getCommandline("$*") << std::endl;
		wrapper << "date +\"End: %s%3N\"" << std::endl;
		wrapper.close();

		std::ofstream out(".jobs." + std::to_string(ID));
		out << "executable = .wrapper_" << ID << std::endl;
		out << "output = out/out." << ID << ".$(cluster).$(process)" << std::endl;
		out << "error = out/err." << ID << ".$(cluster).$(process)" << std::endl;
		out << "log = out/log." << ID << std::endl;
		out << "periodic_hold = (time() - JobCurrentStartExecutingDate) > " << std::chrono::seconds(settings_benchmarks().limit_time).count() << std::endl;
		
		for (const auto& file: b) {
			if (!tool.canHandle(file)) continue;
			out << "transfer_input_files = " << file.native() << ", " << tool.binary().native() << std::endl;
			out << "arguments = " << file.filename().native() << std::endl;
			out << "queue" << std::endl;
		}
		out.close();
		return ".jobs." + std::to_string(ID);
	}
	
	/// Collect job results for the given id.
	void collectResults(std::size_t ID) {
		typedef fs::directory_iterator dirIt;
		
		for (dirIt it("out/"), end; it != end; ++it) {
			std::string name = it->path().native();
			if (name.find("out/out." + std::to_string(ID)) != std::string::npos) {
				
			}
		}
	}
	
	/// Run the given job and wait for its results.
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
	/// Run all tools on all benchmarks.
	void run(const Jobs& jobs) {
		BENCHMAX_LOG_INFO("benchmax.condor", "Generating submit files...");
		
		//for (const auto& tool: tools) {
		//	std::size_t ID = processes.size() + 1;
		//	std::string submitFile = generateSubmitFile(ID, *tool.get(), benchmarks);
		//	processes.emplace_back(false);
		//	std::async(&CondorBackend::runAndWait, this, ID, std::ref(submitFile), std::ref(processes.back()));
		//}
		//while (!processes.empty()) {
		//	while (!processes.front()) usleep(1000000);
		//	assert(processes.front());
		//	processes.pop_front();
		//}
	}
};

}
