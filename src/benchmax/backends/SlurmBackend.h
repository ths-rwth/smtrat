#pragma once

#include "Backend.h"

#include "../logging.h"
#include "../Settings.h"
#include "../utils/Execute.h"
#include "../utils/durations.h"

#include <filesystem>
#include <regex>

namespace benchmax {

class SlurmBackend: public Backend {
private:
	int getJobID(const std::string& output) const {
		std::regex r("Submitted batch job ([0-9]+)");
		std::smatch m;
		if (std::regex_search(output, m, r)) {
			BENCHMAX_LOG_DEBUG("smtrat.slurm", "Job ID is " << m[1]);
			return std::stoi(m[1]);
		} else {
			BENCHMAX_LOG_ERROR("smtrat.slurm", "Unable to obtain job id from slurm output.");
			return -1;
		}
	}

	void parse_result_file(const fs::path& file) const {

	}

	void parse_result_files(const fs::path& basedir) const {
		BENCHMAX_LOG_DEBUG("smtrat.slurm", "Collecting results from " << basedir);

		std::regex filere("# START ([0-9]+) #(.*)# END \1 #(?:(.*)# END DATA \1 #)?");

		for (const auto& f: std::filesystem::directory_iterator(basedir)) {
			std::cout << f.path() << std::endl;
			std::ifstream in(f.path());
			std::string str((std::istreambuf_iterator<char>(in)), std::istreambuf_iterator<char>());
			auto reBegin = sregex_iterator(str.begin(), str.end(), filere);
			auto reEnd = sregex_iterator();
			for (auto i = reBegin; i != reEnd; ++i) {
				std::cout << "Found data for " << (*i)[1] << std::endl;
			}
		}
	}

	std::string generateSubmitFile(const std::string& jobfile, std::size_t num_input) {
		std::string filename = Settings::outputDir + "/job_" + Settings::fileSuffix + ".job";
		BENCHMAX_LOG_DEBUG("smtrat.slurm", "Writing submit file to " << filename);
		std::ofstream out(filename);
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
		out << "tasks=" << num_input << std::endl;
		out << "jobcount=$(( max - min + 1 ))" << std::endl;
		out << "slicesize=$(( (tasks + jobcount + 1) / jobcount ))" << std::endl;
		out << "start=$(( (cur - 1) * slicesize + min ))" << std::endl;
		out << "end=$(( start + slicesize - 1 ))" << std::endl;

		auto timeout = (seconds(Settings::timeLimit) + std::chrono::seconds(3)).count();
		// Execute this slice
		out << "for i in `seq ${start} ${end}`; do" << std::endl;
		out << "\tcmd=$(sed -n \"${i}p\" < " << jobfile << ")" << std::endl;
		out << "\techo \"Executing $cmd\"" << std::endl;
		out << "\techo \"# START ${i} #\"" << std::endl;
		out << "\techo \"# START ${i} #\" >&2" << std::endl;
		out << "\tstart=`date +\"Start: %s%3N\"`" << std::endl;
		out << "\tulimit -S -v " << (Settings::memoryLimit * 1024) << " && ulimit -S -t " << timeout << " && $cmd ; rc=$?" << std::endl;
		out << "\tend=`date +\"End: %s%3N\"`" << std::endl;
		out << "\techo \"# END ${i} #\"" << std::endl;
		out << "\techo \"# END ${i} #\" >&2" << std::endl;
		out << "\techo \"time: $(( end - start ))\"" << std::endl;
		out << "\techo \"exitcode: $rc\"" << std::endl;
		out << "\techo \"# END DATA ${i} #\"" << std::endl;
		out << "done" << std::endl;
		out.close();

		return filename;
	}
public:
	void run(const std::vector<Tool*>& tools, const std::vector<BenchmarkSet>& benchmarks) {

		std::string jobsfile = Settings::outputDir + "/jobs_" + Settings::fileSuffix + ".jobs";
		BENCHMAX_LOG_INFO("benchmax.slurm", "Writing job file to " << jobsfile);
		std::ofstream jobs(jobsfile);
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
		auto submitfile = generateSubmitFile(jobsfile, count);

		BENCHMAX_LOG_INFO("benchmax.slurm", "Submitting job now.");
		std::string output;
		callProgram("sbatch --wait --array=1-1000 -N1 " + submitfile, output);
		BENCHMAX_LOG_INFO("benchmax.slurm", "Job terminated.");

		parse_result_files(Settings::outputDir);
		BENCHMAX_LOG_INFO("benchmax.slurm", "Finished.");
	}
};

}