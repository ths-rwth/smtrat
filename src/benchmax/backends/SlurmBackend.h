#pragma once

#include "Backend.h"

#include "../logging.h"
#include "../utils/Execute.h"
#include "../utils/durations.h"

#include "slurm/SlurmSettings.h"
#include "slurm/SlurmUtilities.h"

#include <algorithm>
#include <filesystem>
#include <random>
#include <regex>

namespace benchmax {

/**
 * Backend for the Slurm workload manager.
 */
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
			auto& res = std::get<3>(mResults[id]);
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
	void run(const Tools& tools, const std::vector<BenchmarkSet>& benchmarks) {

		for (const auto& tool: tools) {
			for (const BenchmarkSet& set: benchmarks) {
				for (const auto& file: set) {
					mResults.emplace_back(JobData { tool.get(), file, set.baseDir(), BenchmarkResult() });
				}
			}
		}
		BENCHMAX_LOG_DEBUG("benchmax.slurm", "Gathered " << mResults.size() << " jobs");
		shuffle_jobs();
		std::string jobsfile = "jobs-" + std::to_string(settings_core().start_time) + ".jobs";
		BENCHMAX_LOG_INFO("benchmax.slurm", "Writing job file to " << jobsfile);
		std::ofstream jobs(settings_slurm().tmp_dir + "/" + jobsfile);
		for (const auto& r: mResults) {
			jobs << std::get<0>(r)->getCommandline(std::get<1>(r)) << std::endl;
		}
		jobs.close();
		auto submitfile = slurm::generate_submit_file({
			std::to_string(settings_core().start_time),
			jobsfile,
			settings_slurm().tmp_dir,
			settings_benchmarks().limit_time,
			settings_benchmarks().limit_memory,
			mResults.size(),
			settings_slurm().slices
		});

		BENCHMAX_LOG_INFO("benchmax.slurm", "Submitting job now.");
		std::string output;
		callProgram("sbatch --wait --array=1-" + std::to_string(settings_slurm().slices) + " -N1 " + settings_slurm().tmp_dir + "/" + submitfile, output, true);
		BENCHMAX_LOG_INFO("benchmax.slurm", "Job terminated, collecting results.");
		int jobid = slurm::parse_job_id(output);

		auto files = slurm::collect_result_files(settings_slurm().tmp_dir, jobid);
		for (const auto& f: files) {
			parse_result_file(f);
		}
		BENCHMAX_LOG_DEBUG("benchmax.slurm", "Parsed results.");
		for (auto& r: mResults) {
			addResult(std::get<0>(r), std::get<1>(r), std::get<2>(r), std::get<3>(r));
		}

		if (settings_slurm().archive_log_file != "") {
			slurm::archive_log_files({
				settings_slurm().archive_log_file,
				jobsfile,
				submitfile,
				settings_slurm().tmp_dir,
				jobid
			});
		}
		slurm::remove_log_files(files, !settings_slurm().keep_logs);

		BENCHMAX_LOG_INFO("benchmax.slurm", "Finished.");
	}
};

}