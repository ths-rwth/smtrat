/**
 * @file CondorBackend.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <cstdlib>
#include <fstream>

#include "Backend.h"
#include "BackendData.h"

#include "../Settings.h"

namespace benchmax {

class CondorBackend: public Backend {
protected:
	virtual void execute(const Tool& tool, const fs::path& file) {
		
	}
	
	std::string generateSubmitFile(const Tool& tool, BenchmarkSet& b) {
		std::ofstream out(".jobs_" + b.benchmarkName());
		out << "executable = " << tool.path() << std::endl;
		out << "output = out/out.$(process)" << std::endl;
		out << "error = out/err.$(process)" << std::endl;
		out << "log = out/log" << std::endl;
		out << "periodic_hold = (time() - JobCurrentStartExecutingDate) > " << Settings::timeLimit << std::endl;
		
		while (!b.done()) {
			auto l = b.pop(1);
			out << "transfer_input_files = " << l.front().native() << std::endl;
			out << "arguments = " << l.front().filename().native() << std::endl;
			out << "queue" << std::endl;
		}
		out.close();
		return ".jobs_" + b.benchmarkName();
	}
	
	void run() {
		BENCHMAX_LOG_INFO("benchmax.condor", "Generating submit files...");
		/*for (auto& b: data->benchmarks) {
			auto filename = generateSubmitFile(*b);
			system(("condor_submit " + filename).c_str());
			system("condor_wait out/log");
		}*/
	}
};

}
