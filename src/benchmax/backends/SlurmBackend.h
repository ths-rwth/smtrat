#pragma once

#include "Backend.h"

#include <benchmax/logging.h>
#include <benchmax/utils/execute.h>

#include "slurm/SlurmSettings.h"
#include "slurm/SlurmUtilities.h"

#include <filesystem>
#include <future>
#include <regex>

namespace benchmax {

/**
 * Backend for the Slurm workload manager.
 * 
 * The execution model is as follows:
 * We create multiple jobs that each consists of multiple array jobs that each execute one slice of the task list.
 * One array job executes Settings::slice_size entries of the task list.
 * One job consists of Settings::array_size array jobs.
 * We start as many jobs as necessary.
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

	void run_job_sync() {
		std::string jobsfilename = "jobs-" + std::to_string(settings_core().start_time) + ".jobs";
		BENCHMAX_LOG_INFO("benchmax.slurm", "Writing job file to " << jobsfilename);
		std::ofstream jobsfile(settings_slurm().tmp_dir + "/" + jobsfilename);
		for (const auto& r: mResults) {
			jobsfile << std::get<0>(r)->getCommandline(std::get<1>(r)) << std::endl;
		}
		jobsfile.close();
		auto slices = std::min(settings_slurm().array_size, mResults.size());
		
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
		BENCHMAX_LOG_INFO("benchmax.slurm", "Finished.");
	}

	void run_job_async(std::size_t n) {
		std::string jobsfilename = "jobs-" + std::to_string(settings_core().start_time) + "-" + std::to_string(n+1) + ".jobs";
		BENCHMAX_LOG_INFO("benchmax.slurm", "Writing job file to " << jobsfilename);
		std::ofstream jobsfile(settings_slurm().tmp_dir + "/" + jobsfilename);
		std::size_t job_size = settings_slurm().array_size * settings_slurm().slice_size;
		std::size_t start = job_size * n;
		std::size_t end = std::max(start + job_size, mResults.size());
		BENCHMAX_LOG_INFO("benchmax.slurm", "Taking jobs " << start << ".." << (end - 1));

		for (std::size_t i = start; i < end; ++i) {
			const auto& r = mResults[i];
			jobsfile << std::get<0>(r)->getCommandline(std::get<1>(r)) << std::endl;
		}
		jobsfile.close();
		
		auto submitfile = slurm::generate_submit_file_chunked({
			std::to_string(settings_core().start_time),
			jobsfilename,
			settings_slurm().tmp_dir,
			settings_benchmarks().limit_time,
			settings_benchmarks().limit_memory,
			settings_slurm().array_size,
			settings_slurm().slice_size
		});

		std::string cmd = "sbatch --wait --array=1-" + std::to_string(settings_slurm().array_size) + " " + settings_slurm().tmp_dir + "/" + submitfile;
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
		slurm::remove_log_files(files, !settings_slurm().keep_logs);
	}
public:
	/// Run all tools on all benchmarks using Slurm.
	void run(const Jobs& jobs) {
		for (const auto& [tool, file]: jobs.randomized()) {
			mResults.emplace_back(JobData { tool, file, BenchmarkResult() });
		}
		BENCHMAX_LOG_DEBUG("benchmax.slurm", "Gathered " << mResults.size() << " jobs");
		
		std::vector<std::future<void>> tasks;
		std::size_t count = mResults.size() / (settings_slurm().array_size * settings_slurm().slice_size) + 1;
		for (std::size_t i = 0; i < count; ++i) {
			tasks.emplace_back(std::async(std::launch::async,
				[i,this](){ return run_job_async(i); }
			));
		}
		for (auto& f: tasks) {
			f.wait();
		}
		BENCHMAX_LOG_DEBUG("benchmax.slurm", "All jobs terminated.");
	}
};

}