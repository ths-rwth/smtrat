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
	if (settings_operation().mode == "both") {
		backend.run(jobs, true);
		backend.process_results(jobs, false);
	} else {
		if (!backend.suspendable()) {
			BENCHMAX_LOG_ERROR("benchmax", "The selected backend cannot be suspended. You need to use mode=\"both\".");
			return;
		}
		if (settings_operation().mode == "execute") {
			backend.run(jobs, false);
		} else if (settings_operation().mode == "collect") {
			backend.process_results(jobs, true);
		} else {
			BENCHMAX_LOG_ERROR("benchmax", "Unsupported operation mode \"" << settings_operation().mode << "\". Use one of \"execute\", \"collect\", \"both\".");
			return;
		}
	}
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