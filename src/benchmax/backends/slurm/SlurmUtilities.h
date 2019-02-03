#pragma once

#include <chrono>
#include <filesystem>
#include <string>
#include <vector>

namespace benchmax {
namespace slurm {

namespace fs = std::filesystem;

struct ArchiveProperties {
	std::string filename_archive;
	std::string filename_jobfile;
	std::string filename_submitfile;
	std::string tmp_dir;
	int jobid;
};
void archive_log_files(const ArchiveProperties& p);

/**
 * Collects all result files in the given base directory for this job id.
 * @param basedir Base directory to search in.
 * @param jobid ID of slurm job.
 * @return List of result files.
 */
std::vector<fs::path> collect_result_files(const fs::path& basedir, int jobid);


struct SubmitfileProperties {
	std::string file_suffix;
	std::string filename_jobs;
	std::string tmp_dir;
	std::chrono::seconds limit_time;
	std::size_t limit_memory;
	std::size_t tasks;
	std::size_t slices;
};

/**
 * Generate a submit file for Slurm with the given properties.
 * @param p Collection of all information needed.
 * @return The filename of the submit file.
 */
std::string generate_submit_file(const SubmitfileProperties& p);

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
 */
void remove_log_files(const std::vector<fs::path>& files, bool remove);

}
}