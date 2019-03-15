#pragma once

#include "CondorBackend.h"
#include "LocalBackend.h"
#include "SlurmBackend.h"
#include "SSHBackend.h"

#include "Jobs.h"

#include <benchmax/logging.h>
#include <benchmax/tools/Tools.h>

namespace benchmax {

template<typename Backend>
void execute_backend(const std::string& name, const Jobs& jobs) {
	BENCHMAX_LOG_INFO("benchmax", "Using " << name << " backend.");
	Backend backend;
	backend.run(jobs);
	backend.sanitize_results(jobs);
	backend.write_results(jobs);
}
/**
 * Runs a given backend on a list of tools and benchmarks.
 * @param backend Backend name.
 * @param tools List of tools.
 * @param benchmarks List of benchmarks.
 */
void run_backend(const std::string& backend, const Jobs& jobs) {
	if (backend == "condor") {
		execute_backend<CondorBackend>(backend, jobs);
	} else if (backend == "local") {
		execute_backend<LocalBackend>(backend, jobs);
	} else if (backend == "slurm") {
		execute_backend<SlurmBackend>(backend, jobs);
	} else if (backend == "ssh") {
		execute_backend<SSHBackend>(backend, jobs);
	} else {
		BENCHMAX_LOG_ERROR("benchmax", "Invalid backend \"" << settings_operation().backend << "\".");
	}
}

}