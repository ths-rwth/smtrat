#pragma once

#include "Backend.h"

#include <benchmax/logging.h>
#include <benchmax/utils/execute.h>

#include "slurm/SlurmSettings.h"
#include "slurm/SlurmUtilities.h"

#include <filesystem>
#include <future>
#include <mutex>
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
	
	/// Mutex for submission delay.
	std::mutex mSubmissionMutex;

	/// Parse the content of an output file.
	void parse_result_file(const Jobs& jobs, const std::filesystem::path& file, std::vector<JobData>& results) {
		BENCHMAX_LOG_DEBUG("benchmax.slurm", "Processing file " << file);
		std::ifstream in(file);
		std::string content((std::istreambuf_iterator<char>(in)), std::istreambuf_iterator<char>());
		auto extension = file.extension();
		std::regex filere("Executing (.+)\\n# START ([0-9]+) #([^#]*)# END \\2 #(?:([^#]*)# END DATA \\2 #)?");

		auto reBegin = std::sregex_iterator(content.begin(), content.end(), filere);
		auto reEnd = std::sregex_iterator();
		for (auto i = reBegin; i != reEnd; ++i) {
			std::size_t id = std::stoull((*i)[2]) - 1;
			bool toolFound = false;
			std::string cmdline = (*i)[1];
			for (const auto& tool : jobs.tools()) {
				auto t = tool->parseCommandline(cmdline);
				if (t) {
					results.emplace_back(JobData { tool.get(), std::filesystem::path(*t), BenchmarkResult() });
					toolFound = true;
					break;
				}
			}
			if (!toolFound) {
				BENCHMAX_LOG_WARN("benchmax.slurm", "Could not find tool for " << cmdline);
			} else {
				auto& res = std::get<2>(results.back());
				if (extension == ".out") {
					res.stdout = (*i)[3];
					res.exitCode = std::stoi(slurm::parse_result_info((*i)[4], "exitcode"));
					res.time = std::chrono::milliseconds(std::stoi(slurm::parse_result_info((*i)[4], "time")));
					BENCHMAX_LOG_DEBUG("benchmax.slurm", "Got " << res << " for task " << id << " from stdout");
				} else if (extension == ".err") {
					res.stderr = (*i)[3];
					BENCHMAX_LOG_DEBUG("benchmax.slurm", "Got " << res << " for task " << id << " from stderr");
				} else {
					BENCHMAX_LOG_WARN("benchmax.slurm", "Trying to parse output file with unexpected extension " << extension);
				}
			}
		}
	}

	std::pair<std::size_t,std::size_t> get_job_range(std::size_t n, std::size_t numJobs) const {
		std::size_t job_size = settings_slurm().array_size * settings_slurm().slice_size;
		return std::make_pair(
			job_size * n,
			std::min(job_size * (n + 1), numJobs)
		);
	}

	void store_job_id(int jobid) {
		mSlurmjobMutex.lock();
		std::ofstream out(settings_slurm().tmp_dir + "/slurmjobs", std::ios_base::app);
		out << jobid << std::endl;
		out.close();
	}

	std::vector<int> load_job_ids() {
		std::vector<int> res;
		std::ifstream in(settings_slurm().tmp_dir + "/slurmjobs");
		if (!in) {
			return res;
		}
		int jobid;
		while(in >> jobid) {
			res.push_back(jobid);
		}
		in.close();
		return res;
	}

	void remove_job_ids() {
		if( std::remove( (settings_slurm().tmp_dir + "/slurmjobs").c_str() ) != 0 ){
			BENCHMAX_LOG_WARN("benchmax.slurm", settings_slurm().tmp_dir + "/slurmjobs file could not be deleted");
		}
	}

	void run_job_async(std::size_t n, const std::vector<JobData>& results, bool wait_for_termination) {
		std::string jobsfilename = settings_slurm().tmp_dir + "/jobs-" + std::to_string(settings_core().start_time) + "-" + std::to_string(n+1) + ".jobs";
		slurm::generate_jobs_file(jobsfilename, get_job_range(n, results.size()), results);

		auto submitfile = slurm::generate_submit_file_chunked({
			std::to_string(settings_core().start_time) + "-" + std::to_string(n),
			jobsfilename,
			settings_slurm().tmp_dir,
			settings_benchmarks().limit_time,
			settings_benchmarks().grace_time,
			settings_benchmarks().limit_memory,
			settings_slurm().array_size,
			settings_slurm().slice_size
		});

		BENCHMAX_LOG_INFO("benchmax.slurm", "Delaying for " << settings_slurm().submission_delay);
		{
			std::lock_guard<std::mutex> guard(mSubmissionMutex);
			std::this_thread::sleep_for(settings_slurm().submission_delay);
		}
		BENCHMAX_LOG_INFO("benchmax.slurm", "Submitting job now.");

		std::stringstream cmd;
		cmd << "sbatch";
		if (wait_for_termination) cmd << " --wait";
		cmd << " --array=1-" << std::to_string(settings_slurm().array_size);
		cmd << " " << settings_slurm().sbatch_options;
		cmd << " " + submitfile;
		BENCHMAX_LOG_DEBUG("benchmax.slurm", "Command: " << cmd.str());
		std::string output;
		call_program(cmd.str(), output, true);
		int jobid = slurm::parse_job_id(output);
		if (wait_for_termination) {
			BENCHMAX_LOG_INFO("benchmax.slurm", "Job terminated.");
		} else {
			BENCHMAX_LOG_INFO("benchmax.slurm", "Job " << jobid << " was scheduled.");
		}
	}

	bool collect_results(const Jobs& jobs, bool check_finished) override {
		if (check_finished) {
			BENCHMAX_LOG_INFO("benchmax.slurm", "Check if job finished.");
			auto jobids = load_job_ids();
			if (jobids.size() == 0) {
				BENCHMAX_LOG_ERROR("benchmax.slurm", "Jobids could not be determined!");
				return false;
			}
			for (int jobid : jobids) {
				if (!slurm::is_job_finished(jobid)) {
					BENCHMAX_LOG_WARN("benchmax.slurm", "Job " << jobid << " is not finished yet.");
					return false;
				}
			}
			remove_job_ids();
		}

		BENCHMAX_LOG_INFO("benchmax.slurm", "Collecting results.");
		std::vector<JobData> results;
		auto files = slurm::collect_result_files(settings_slurm().tmp_dir);
		for (const auto& f: files) {
			parse_result_file(jobs, f, results);
		}
		BENCHMAX_LOG_DEBUG("benchmax.slurm", "Parsed results.");
		for (auto& r: results) {
			addResult(std::get<0>(r), std::get<1>(r), std::get<2>(r));
		}
		if (settings_slurm().archive_log_file != "") {
			slurm::archive_log_files({
				settings_slurm().archive_log_file + "-" + std::to_string(settings_core().start_time) + ".tgz",
				settings_slurm().tmp_dir
			});
		}
		slurm::remove_log_files(files, !settings_slurm().keep_logs);
	}
public:
	bool suspendable() const {
		return true;
	}
	/// Run all tools on all benchmarks using Slurm.
	void run(const Jobs& jobs, bool wait_for_termination) {
		if (load_job_ids().size() > 0) {
			BENCHMAX_LOG_ERROR("benchmax.slurm", "Benchmax is still running in the specified tmp_dir! If this is not the case, please delete " + settings_slurm().tmp_dir + "/slurmjobs");
			return;
		}

		std::vector<JobData> results;
		for (const auto& [tool, file]: jobs.randomized()) {
			results.emplace_back(JobData { tool, file, BenchmarkResult() });
		}
		BENCHMAX_LOG_DEBUG("benchmax.slurm", "Gathered " << results.size() << " jobs");
		
		std::vector<std::future<void>> tasks;
		std::size_t count = results.size() / (settings_slurm().array_size * settings_slurm().slice_size) + 1;
		for (std::size_t i = 0; i < count; ++i) {
			tasks.emplace_back(std::async(std::launch::async,
				[i,&results,wait_for_termination,this](){
					return run_job_async(i, results, wait_for_termination);
				}
			));
		}
		for (auto& f: tasks) {
			f.wait();
		}
		BENCHMAX_LOG_DEBUG("benchmax.slurm", "All jobs terminated.");
	}
};

}