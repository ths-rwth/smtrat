#include "SlurmUtilities.h"

#include <regex>
#include <sstream>

#include <benchmax/logging.h>
#include <benchmax/utils/execute.h>

namespace benchmax {
namespace slurm {

void archive_log_files(const ArchiveProperties& p) {
	std::string output;
	std::stringstream ss;
	ss << "tar -czf " << p.filename_archive << " ";
	ss << "-C " << p.tmp_dir << " ";
	ss << p.filename_jobfile << " " << p.filename_submitfile << " ";
	ss << "`find " << p.tmp_dir << " -iname \"JOB." << p.jobid << "_*\"`";
	BENCHMAX_LOG_DEBUG("benchmax.slurm", "Archiving log files with command " << ss.str());
	int code = call_program(ss.str(), output);
	if (code == 0) {
		BENCHMAX_LOG_INFO("benchmax.slurm", "Archived log files in " << p.filename_archive << " from " << p.tmp_dir);
	} else {
		BENCHMAX_LOG_WARN("benchmax.slurm", "Archiving of log files failed with exit code " << code);
		BENCHMAX_LOG_WARN("benchmax.slurm", output);
	}
}

std::vector<fs::path> collect_result_files(const fs::path& basedir, int jobid) {
	BENCHMAX_LOG_DEBUG("benchmax.slurm", "Collecting results files from " << basedir);
	std::vector<fs::path> files;

	std::regex filenamere("JOB." + std::to_string(jobid) + "_[0-9]+.(out|err)");
	for (const auto& f: fs::directory_iterator(basedir)) {
		if (!std::regex_match(f.path().filename().string(), filenamere)) {
			BENCHMAX_LOG_TRACE("benchmax.slurm", "Skipping file " << f.path());
			continue;
		}
		BENCHMAX_LOG_DEBUG("benchmax.slurm", "Using file " << f.path());
		files.emplace_back(f.path());
	}
	BENCHMAX_LOG_INFO("benchmax.slurm", "Collected " << files.size() << " log files.");
	return files;
}

std::string generate_submit_file(const SubmitfileProperties& p) {
	std::string filename = "job-" + p.file_suffix + ".job";
	BENCHMAX_LOG_DEBUG("benchmax.slurm", "Writing submit file to " << p.tmp_dir << "/" << filename);
	std::ofstream out(p.tmp_dir + "/" + filename);
	out << "#!/usr/bin/env zsh" << std::endl;
	out << "### Job name" << std::endl;
	// Job name
	out << "#SBATCH --job-name=benchmax" << std::endl;
	// Output files (stdout and stderr)
	out << "#SBATCH -o " << p.tmp_dir << "/JOB.%A_%a.out" << std::endl;
	out << "#SBATCH -e " << p.tmp_dir << "/JOB.%A_%a.err" << std::endl;
	// Rough estimation of time in minutes (timeout * jobs)
	auto minutes = static_cast<std::size_t>(std::chrono::seconds(p.limit_time).count() + 10) * p.tasks / p.slices / 60 + 1;
	minutes = std::min(minutes, static_cast<std::size_t>(60*24));
	out << "#SBATCH -t " << minutes << std::endl;
	// Memory usage in MB
	out << "#SBATCH --mem-per-cpu=" << (p.limit_memory + 1024) << "M" << std::endl;

	// Load environment
	out << "source ~/load_environment" << std::endl;
	// Change current directory
	out << "cd " << p.tmp_dir << std::endl;

	// Calculate slices for jobfile
	out << "min=$SLURM_ARRAY_TASK_MIN" << std::endl;
	out << "max=$SLURM_ARRAY_TASK_MAX" << std::endl;
	out << "cur=$SLURM_ARRAY_TASK_ID" << std::endl;
	out << "tasks=" << p.tasks << std::endl;
	out << "jobcount=$(( max - min + 1 ))" << std::endl;
	out << "slicesize=$(( (tasks + jobcount + 1) / jobcount ))" << std::endl;
	out << "start=$(( (cur - 1) * slicesize + min ))" << std::endl;
	out << "end=$(( start + slicesize - 1 ))" << std::endl;

	auto timeout = (std::chrono::seconds(p.limit_time) + std::chrono::seconds(3)).count();
	// Execute this slice
	out << "for i in `seq ${start} ${end}`; do" << std::endl;
	out << "\tcmd=$(sed -n \"${i}p\" < " << p.filename_jobs << ")" << std::endl;
	out << "\techo \"Executing $cmd\"" << std::endl;
	out << "\techo \"# START ${i} #\"" << std::endl;
	out << "\techo \"# START ${i} #\" >&2" << std::endl;
	out << "\tstart=`date +\"%s%3N\"`" << std::endl;
	out << "\tulimit -c 0 && ulimit -S -v " << (p.limit_memory * 1024) << " && ulimit -S -t " << timeout << " && $cmd ; rc=$?" << std::endl;
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


std::string generate_submit_file_chunked(const ChunkedSubmitfileProperties& p) {
	std::string filename = "job-" + p.file_suffix + ".job";
	BENCHMAX_LOG_DEBUG("benchmax.slurm", "Writing submit file to " << p.tmp_dir << "/" << filename);
	std::ofstream out(p.tmp_dir + "/" + filename);
	out << "#!/usr/bin/env zsh" << std::endl;
	out << "### Job name" << std::endl;
	// Job name
	out << "#SBATCH --job-name=benchmax" << std::endl;
	// Output files (stdout and stderr)
	out << "#SBATCH -o " << p.tmp_dir << "/JOB.%A_%a.out" << std::endl;
	out << "#SBATCH -e " << p.tmp_dir << "/JOB.%A_%a.err" << std::endl;
	// Rough estimation of time in minutes (timeout * slice_size)
	long minutes = (std::chrono::seconds(p.limit_time) * p.slice_size).count() / 60;
	minutes = std::min(minutes + 1, static_cast<long>(60*24));
	out << "#SBATCH -t " << minutes << std::endl;
	// Memory usage in MB
	out << "#SBATCH --mem-per-cpu=" << (p.limit_memory + 1024) << "M" << std::endl;

	// Load environment
	out << "source ~/load_environment" << std::endl;
	// Change current directory
	out << "cd " << p.tmp_dir << std::endl;

	// Calculate slices for jobfile
	out << "min=$SLURM_ARRAY_TASK_MIN" << std::endl;
	out << "max=$SLURM_ARRAY_TASK_MAX" << std::endl;
	out << "cur=$SLURM_ARRAY_TASK_ID" << std::endl;
	out << "slicesize=" << p.slice_size << std::endl;
	out << "start=$(( (cur - 1) * slicesize ))" << std::endl;
	out << "end=$(( start + slicesize - 1 ))" << std::endl;

	auto timeout = (std::chrono::seconds(p.limit_time) + std::chrono::seconds(3)).count();
	// Execute this slice
	out << "for i in `seq ${start} ${end}`; do" << std::endl;
	out << "\tcmd=$(sed -n \"${i}p\" < " << p.filename_jobs << ")" << std::endl;
	out << "\techo \"Executing $cmd\"" << std::endl;
	out << "\techo \"# START ${i} #\"" << std::endl;
	out << "\techo \"# START ${i} #\" >&2" << std::endl;
	out << "\tstart=`date +\"%s%3N\"`" << std::endl;
	out << "\tulimit -c 0 && ulimit -S -v " << (p.limit_memory * 1024) << " && ulimit -S -t " << timeout << " && $cmd ; rc=$?" << std::endl;
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

int parse_job_id(const std::string& output) {
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

std::string parse_result_info(const std::string& content, const std::string& name) {
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

void remove_log_files(const std::vector<fs::path>& files, bool remove) {
	if (remove) {
		BENCHMAX_LOG_INFO("benchmax.slurm", "Removing log files.");
		for (const auto& f: files) {
			std::filesystem::remove(f);
		}
	} else {
		BENCHMAX_LOG_INFO("benchmax.slurm", "Retaining log files.");
	}
}

}
}