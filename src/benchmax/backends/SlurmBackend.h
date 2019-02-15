#pragma once

#include "Backend.h"

#include <benchmax/logging.h>
#include <benchmax/utils/execute.h>

#include "slurm/SlurmSettings.h"
#include "slurm/SlurmUtilities.h"

#include <filesystem>
#include <regex>

namespace benchmax {

/**
 * Backend for the Slurm workload manager.
 */
class SlurmBackend: public Backend {
private:
	/// A job consists of a tool, an input file, a base dir and results.
	using JobData = std::tuple<
		const Tool*,
		std::filesystem::path,
		BenchmarkResult
	>;
	
	/// All jobs.
	std::vector<JobData> mResults;

	/// Parse the content of an output file.
	void parse_result_file(const std::filesystem::path& file) {
		BENCHMAX_LOG_DEBUG("benchmax.slurm", "Processing file " << file);
		std::ifstream in(file);
		std::string content((std::istreambuf_iterator<char>(in)), std::istreambuf_iterator<char>());
		auto extension = file.extension();
		std::regex filere("# START ([0-9]+) #((?:.|\n)*)# END \\1 #(?:((?:.|\n)*)# END DATA \\1 #)?");

		auto reBegin = std::sregex_iterator(content.begin(), content.end(), filere);
		auto reEnd = std::sregex_iterator();
		for (auto i = reBegin; i != reEnd; ++i) {
			assert(std::stoi((*i)[1]) > 0);
			std::size_t id = std::stoull((*i)[1]) - 1;
			if (id >= mResults.size()) continue;
			auto& res = std::get<2>(mResults[id]);
			if (extension == ".out") {
				res.stdout = (*i)[2];
				res.exitCode = std::stoi(slurm::parse_result_info((*i)[3], "exitcode"));
				res.time = std::chrono::milliseconds(std::stoi(slurm::parse_result_info((*i)[3], "time")));
				BENCHMAX_LOG_DEBUG("benchmax.slurm", "Got " << res << " for task " << id << " from stdout");
			} else if (extension == ".err") {
				res.stderr = (*i)[2];
				BENCHMAX_LOG_DEBUG("benchmax.slurm", "Got " << res << " for task " << id << " from stderr");
			} else {
				BENCHMAX_LOG_WARN("benchmax.slurm", "Trying to parse output file with unexpected extension " << extension);
			}
		}
	}
public:
	/// Run all tools on all benchmarks using Slurm.
	void run(const Jobs& jobs) {
		for (const auto& [tool, file]: jobs.randomized()) {
			mResults.emplace_back(JobData { tool, file, BenchmarkResult() });
		}
		BENCHMAX_LOG_DEBUG("benchmax.slurm", "Gathered " << mResults.size() << " jobs");
		std::string jobsfilename = "jobs-" + std::to_string(settings_core().start_time) + ".jobs";
		BENCHMAX_LOG_INFO("benchmax.slurm", "Writing job file to " << jobsfilename);
		std::ofstream jobsfile(settings_slurm().tmp_dir + "/" + jobsfilename);
		for (const auto& r: mResults) {
			jobsfile << std::get<0>(r)->getCommandline(std::get<1>(r)) << std::endl;
		}
		jobsfile.close();
		auto slices = std::min(settings_slurm().slices, mResults.size());
		
		auto submitfile = slurm::generate_submit_file({
			std::to_string(settings_core().start_time),
			jobsfilename,
			settings_slurm().tmp_dir,
			settings_benchmarks().limit_time,
			settings_benchmarks().limit_memory,
			mResults.size(),
			slices
		});

		std::string cmd = "sbatch --wait --array=1-" + std::to_string(slices) + " " + settings_slurm().tmp_dir + "/" + submitfile;
		BENCHMAX_LOG_INFO("benchmax.slurm", "Submitting job now.");
		BENCHMAX_LOG_DEBUG("benchmax.slurm", "Command: " << cmd);
		std::string output;
		call_program(cmd, output, true);
		BENCHMAX_LOG_INFO("benchmax.slurm", "Job terminated, collecting results.");
		int jobid = slurm::parse_job_id(output);

		auto files = slurm::collect_result_files(settings_slurm().tmp_dir, jobid);
		for (const auto& f: files) {
			parse_result_file(f);
		}
		BENCHMAX_LOG_DEBUG("benchmax.slurm", "Parsed results.");
		for (auto& r: mResults) {
			addResult(std::get<0>(r), std::get<1>(r), std::get<2>(r));
		}

		if (settings_slurm().archive_log_file != "") {
			slurm::archive_log_files({
				settings_slurm().archive_log_file,
				jobsfilename,
				submitfile,
				settings_slurm().tmp_dir,
				jobid
			});
		}
		slurm::remove_log_files(files, !settings_slurm().keep_logs);

		write_results(jobs);
		BENCHMAX_LOG_INFO("benchmax.slurm", "Finished.");
	}
};

}