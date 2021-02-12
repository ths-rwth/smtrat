#pragma once

#include <carl-settings/settings_utils.h>
#include <benchmax/logging.h>

#include <chrono>
#include <filesystem>
#include <string>
#include <vector>

namespace benchmax {
namespace slurm {

namespace fs = std::filesystem;

/// All properties needed to archive log files.
struct ArchiveProperties {
	/// Filename of the archive.
	std::string filename_archive;
	/// Temporary directory to look for output files.
	std::string tmp_dir;
};
/// Put all log files into an archive.
void archive_log_files(const ArchiveProperties& p);

/**
 * Collects all result files in the given base directory for this job id.
 * @param basedir Base directory to search in.
 * @param jobid ID of slurm job.
 * @return List of result files.
 */
std::vector<fs::path> collect_result_files(const fs::path& basedir);

/// All properties needed to create a submit file.
struct SubmitfileProperties {
	/// Suffix for job and submit file.
	std::string file_suffix;
	/// Filename of the job list file.
	std::string filename_jobs;
	/// Temporary directory for log files.
	std::string tmp_dir;
	/// Time limit in seconds.
	carl::settings::duration limit_time;
	/// Grace time in seconds.
	carl::settings::duration grace_time;
	/// Memory limit in megabytes.
	carl::settings::binary_quantity limit_memory;
	/// Number of tasks.
	std::size_t tasks;
	/// Number of slices.
	std::size_t slices;
};

/**
 * Generate a submit file for Slurm with the given properties.
 * @param p Collection of all information needed.
 * @return The filename of the submit file.
 */
std::string generate_submit_file(const SubmitfileProperties& p);

/// All properties needed to create a submit file.
struct ChunkedSubmitfileProperties {
	/// Suffix for job and submit file.
	std::string file_suffix;
	/// Filename of the job list file.
	std::string filename_jobs;
	/// Temporary directory for log files.
	std::string tmp_dir;
	/// Time limit in seconds.
	carl::settings::duration limit_time;
	/// Grace time in seconds.
	carl::settings::duration grace_time;
	/// Memory limit in megabytes.
	carl::settings::binary_quantity limit_memory;
	/// Array size.
	std::size_t array_size;
	/// Slice size.
	std::size_t slice_size;
	/// This slice size.
	std::size_t this_slice_size;
};

std::string generate_submit_file_chunked(const ChunkedSubmitfileProperties& p);

template<typename Jobs>
void generate_jobs_file(const std::string& filename, std::pair<std::size_t,std::size_t> range, const Jobs& jobs) {
	BENCHMAX_LOG_DEBUG("benchmax.slurm", "Writing job file to " << filename);
	std::ofstream jobsfile(filename);
	BENCHMAX_LOG_DEBUG("benchmax.slurm", "Taking jobs " << range.first << ".." << (range.second-1));

	for (std::size_t i = range.first; i < range.second; ++i) {
		const auto& r = jobs[i];
		jobsfile << std::get<0>(r)->getCommandline(std::get<1>(r)) << std::endl;
	}
	jobsfile.close();
	BENCHMAX_LOG_DEBUG("benchmax.slurm", "Job file is finished.");
}

/**
 * Parses the job id from the output of `sbatch`.
 * @param output Output of `sbatch`.
 * @return Slurm job id.
 */
int parse_job_id(const std::string& output);

/**
 * Parse a single result information from the output.
 * @param content Result information output.
 * @param name Information to be parsed.
 * @return Information specified in the output.
 */
std::string parse_result_info(const std::string& content, const std::string& name);

/**
 * Remove the given list of files.
 * @param files List of files.
 * @param remove Boolean flag whether to actually remove files.
 */
void remove_log_files(const std::vector<fs::path>& files, bool remove);

/**
 * Clear log files from directory
 * @param basedir Base directory to search in.
 */
void clear_log_files(const fs::path& basedir);

/**
 * Checks if the given job is finished.
 * @param jobid The job id.
 * @return True if the job is completed.
 */
bool is_job_finished(int jobid);

}
}