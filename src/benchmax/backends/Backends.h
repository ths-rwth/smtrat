#pragma once

#include "CondorBackend.h"
#include "LocalBackend.h"
#include "SlurmBackend.h"
#include "SSHBackend.h"

#include <benchmax/logging.h>
#include <benchmax/tools/Tools.h>

namespace benchmax {

/**
 * Runs a given backend on a list of tools and benchmarks.
 * @param backend Backend name.
 * @param tools List of tools.
 * @param benchmarks List of benchmarks.
 */
void run_backend(const std::string& backend, const Tools& tools, const BenchmarkSet& benchmarks) {

	if (backend == "condor") {
		BENCHMAX_LOG_INFO("benchmax", "Using condor backend.");
		CondorBackend backend;
		backend.run(tools, benchmarks);
	} else if (backend == "local") {
		BENCHMAX_LOG_INFO("benchmax", "Using local backend.");
		LocalBackend backend;
		backend.run(tools, benchmarks);
	} else if (backend == "slurm") {
		BENCHMAX_LOG_INFO("benchmax", "Using slurm backend.");
		SlurmBackend backend;
		backend.run(tools, benchmarks);
	} else if (backend == "ssh") {
		BENCHMAX_LOG_INFO("benchmax", "Using ssh backend.");
		SSHBackend backend;
		backend.run(tools, benchmarks);
	} else {
		BENCHMAX_LOG_ERROR("benchmax", "Invalid backend \"" << settings_operation().backend << "\".");
	}
}

}