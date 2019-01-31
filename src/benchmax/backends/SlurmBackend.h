#pragma once

#include "Backend.h"

#include "../logging.h"
#include "../Settings.h"
#include "../utils/Execute.h"
#include "../utils/durations.h"

#include <algorithm>
#include <filesystem>
#include <random>
#include <regex>

namespace benchmax {

class SlurmBackend: public Backend {
private:
	using JobData = std::tuple<
		const Tool*,
		std::filesystem::path,
		std::filesystem::path,
		BenchmarkResult
	>;
	
	std::vector<JobData> mResults;

	void shuffle_jobs() {
		BENCHMAX_LOG_DEBUG("benchmax.slurm", "Shuffling jobs");
		std::mt19937 rand(mResults.size());
		std::shuffle(mResults.begin(), mResults.end(), rand);
	}
	
	int getJobID(const std::string& output) const {
		std::regex r("Submitted batch job ([0-9]+)");
		std::smatch m;
		if (std::regex_search(output, m, r)) {
			BENCHMAX_LOG_DEBUG("benchmax.slurm", "Job ID is " << m[1]);
			return std::stoi(m[1]);
		} else {
			BENCHMAX_LOG_ERROR("benchmax.slurm", "Unable to obtain job id from slurm output.");
			return -1;
		}
	}
	
	std::string parse_result_info(const std::string& content, const std::string& name) const {
		std::regex re(name + ": (.*)");
		std::smatch m;
		if (std::regex_search(content, m, re)) {
			BENCHMAX_LOG_TRACE("benchmax.slurm", "Retrieved " << name << " = " << m[1]);
			return m[1];
		} else {
			BENCHMAX_LOG_INFO("benchmax.slurm", "Did not find expected information " << name << " in " << content);
			return "";
		}
	}

	void parse_result_file(const std::string& content, const std::string& extension) {
		std::regex filere("# START ([0-9]+) #((?:.|\n)*)# END \\1 #(?:((?:.|\n)*)# END DATA \\1 #)?");

		auto reBegin = sregex_iterator(content.begin(), content.end(), filere);
		auto reEnd = sregex_iterator();
		for (auto i = reBegin; i != reEnd; ++i) {
			assert(std::stoi((*i)[1]) > 0);
			std::size_t id = std::stoull((*i)[1]) - 1;
			if (id >= mResults.size()) continue;
			auto& res = std::get<3>(mResults[id]);
			if (extension == ".out") {
				res.stdout = (*i)[2];
				res.exitCode = std::stoi(parse_result_info((*i)[3], "exitcode"));
				res.time = std::chrono::milliseconds(std::stoi(parse_result_info((*i)[3], "time")));
				BENCHMAX_LOG_DEBUG("benchmax.slurm", "Got " << res << " for task " << id << " from stdout");
			} else if (extension == ".err") {
				res.stderr = (*i)[2];
				BENCHMAX_LOG_DEBUG("benchmax.slurm", "Got " << res << " for task " << id << " from stderr");
			} else {
				BENCHMAX_LOG_WARN("benchmax.slurm", "Trying to parse output file with unexpected extension " << extension);
			}
			
			
		}
	}

	void parse_result_files(const fs::path& basedir, int jobid) {
		BENCHMAX_LOG_DEBUG("benchmax.slurm", "Collecting results from " << basedir);

		std::regex filenamere("JOB." + std::to_string(jobid) + "_[0-9]+.(out|err)");

		for (const auto& f: std::filesystem::directory_iterator(basedir)) {
			if (!std::regex_match(f.path().filename().string(), filenamere)) {
				BENCHMAX_LOG_TRACE("benchmax.slurm", "Skipping file " << f.path());
				continue;
			}
			BENCHMAX_LOG_DEBUG("benchmax.slurm", "Processing file " << f.path());
			std::ifstream in(f.path());
			std::string str((std::istreambuf_iterator<char>(in)), std::istreambuf_iterator<char>());
			parse_result_file(str, f.path().extension());
		}
	}

	std::string generateSubmitFile(const std::string& jobfile, std::size_t num_input) {
		std::string filename = Settings::outputDir + "/job_" + Settings::fileSuffix + ".job";
		BENCHMAX_LOG_DEBUG("benchmax.slurm", "Writing submit file to " << filename);
		std::ofstream out(filename);
		out << "#!/usr/bin/env zsh" << std::endl;
		out << "### Job name" << std::endl;
		// Job name
		out << "#SBATCH --job-name=benchmax" << std::endl;
		// Output files (stdout and stderr)
		out << "#SBATCH -o " << Settings::outputDir << "/JOB.%A_%a.out" << std::endl;
		out << "#SBATCH -e " << Settings::outputDir << "/JOB.%A_%a.err" << std::endl;
		// Rough estimation of time in minutes (timeout * jobs)
		out << "#SBATCH -t " << (static_cast<std::size_t>(seconds(Settings::timeLimit).count()) * num_input / 60 + 1) << std::endl;
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
		out << "\tstart=`date +\"%s%3N\"`" << std::endl;
		out << "\tulimit -S -v " << (Settings::memoryLimit * 1024) << " && ulimit -S -t " << timeout << " && $cmd ; rc=$?" << std::endl;
		out << "\tend=`date +\"%s%3N\"`" << std::endl;
		out << "\techo \"# END ${i} #\"" << std::endl;
		out << "\techo \"# END ${i} #\" 1>&2" << std::endl;
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
		for (const Tool* tool: tools) {
			for (const BenchmarkSet& set: benchmarks) {
				for (const auto& file: set) {
					mResults.emplace_back(JobData { tool, file, set.baseDir(), BenchmarkResult() });
				}
			}
		}
		BENCHMAX_LOG_DEBUG("benchmax.slurm", "Gathered " << mResults.size() << " jobs");
		shuffle_jobs();
		BENCHMAX_LOG_INFO("benchmax.slurm", "Writing job file to " << jobsfile);
		std::ofstream jobs(jobsfile);
		for (const auto& r: mResults) {
			jobs << std::get<0>(r)->getCommandline(std::get<2>(r)) << std::endl;
		}
		jobs.close();
		auto submitfile = generateSubmitFile(jobsfile, mResults.size());
/*
		BENCHMAX_LOG_INFO("benchmax.slurm", "Submitting job now.");
		std::string output;
		callProgram("sbatch --wait --array=1-100 -N1 " + submitfile, output);
		BENCHMAX_LOG_INFO("benchmax.slurm", "Job terminated.");
		
		int jobid = getJobID(output);
*/
		int jobid = 110492;
		parse_result_files(Settings::outputDir, jobid);
		for (auto& r: mResults) {
			addResult(std::get<0>(r), std::get<1>(r), std::get<2>(r), std::get<3>(r));
		}
		BENCHMAX_LOG_INFO("benchmax.slurm", "Finished.");
	}
};

}