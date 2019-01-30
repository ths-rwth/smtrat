#pragma once

#include "Backend.h"

#include "../logging.h"
#include "../Settings.h"
#include "../utils/durations.h"

namespace benchmax {

class SlurmBackend: public Backend {
private:
	static constexpr std::size_t num_slices = 1000;
	void generateJobFile(const std::string& jobfile, std::size_t num_input) {
		std::ofstream out("job_" + Settings::fileSuffix + ".job");
		out << "#!/usr/bin/env zsh" << std::endl;
		out << "### Job name" << std::endl;
		// Job name
		out << "#SBATCH --job-name=benchmax" << std::endl;
		// Output files (stdout and stderr)
		out << "#SBATCH -o " << Settings::outputDir << "/JOB.%A_%a.out" << std::endl;
		out << "#SBATCH -e " << Settings::outputDir << "/JOB.%A_%a.err" << std::endl;
		// Rough estimation of time in minutes (timeout * jobs)
		out << "#SBATCH -t " << (seconds(Settings::timeLimit).count() * num_input / 60 + 1) << std::endl;
		// Memory usage in MB
		out << "#SBATCH --mem-per-cpu=" << (Settings::memoryLimit + 1024) << "M" << std::endl;

		// Load environment
		out << "source ~/load_environment" << std::endl;
		// Change current directory
		out << "cd " << Settings::outputDir << std::endl;

		// Calculate slices for jobfile
		out << "min=$SLURM_ARRAY_TASK_MIN" << std::endl;
		out << "max=$SLURM_ARRAY_TASK_MAX" << std::endl;
		out << "cur=$SLURM_ARRAY_TASK_ID" << std::endl;
		out << "tasks=" << num_slices << std::endl;
		out << "jobcount=$(( max - min + 1 ))" << std::endl;
		out << "slicesize=$(( (tasks + jobcount + 1) / jobcount ))" << std::endl;
		out << "start=$(( (cur - 1) * slicesize + min ))" << std::endl;
		out << "end=$(( start + slicesize - 1 ))" << std::endl;

		auto timeout = (seconds(Settings::timeLimit) + std::chrono::seconds(3)).count();
		// Execute this slice
		out << "for i in `seq ${start} ${end}`; do" << std::endl;
		out << "\tcmd=$(sed -n \"${i}p\" < " << jobfile << ")" << std::endl;
		out << "\techo \"Executing $cmd\"" << std::endl;
		out << "\tdate +\"Start: %s%3N\"" << std::endl;
		out << "\tulimit -S -v " << (Settings::memoryLimit * 1024) << " && ulimit -S -t " << timeout << " && time $cmd ; rc=$?" << std::endl;
		out << "\tdate +\"End: %s%3N\"" << std::endl;
		out << "\techo \"Exit code: $rc\"" << std::endl;
		out << "done" << std::endl;
		out.close();
	}
public:
	void run(const std::vector<Tool*>& tools, const std::vector<BenchmarkSet>& benchmarks) {
		BENCHMAX_LOG_INFO("benchmax.slurm", "Generating ");

		std::string jobfile = Settings::outputDir + "/jobs_" + Settings::fileSuffix + ".jobs";
		std::ofstream jobs(jobfile);
		std::size_t count = 0;
		for (const Tool* tool: tools) {
			for (const BenchmarkSet& set: benchmarks) {
				for (const auto& file: set) {
					jobs << tool->getCommandline(file) << std::endl;
					++count;
				}
			}
		}
		jobs.close();
		generateJobFile(jobfile, count);
	}
};

}