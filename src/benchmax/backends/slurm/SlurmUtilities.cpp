#include "SlurmUtilities.h"

#include <regex>
#include <sstream>

#include <benchmax/utils/execute.h>

namespace benchmax {
namespace slurm {

void archive_log_files(const ArchiveProperties& p) {
	std::string output;
	std::stringstream ss;
	ss << "tar --force-local -czf " << p.filename_archive << " ";
	ss << "-C " << p.tmp_dir << " ";
	ss << "`ls " << p.tmp_dir << "`";
	BENCHMAX_LOG_DEBUG("benchmax.slurm", "Archiving log files with command " << ss.str());
	int code = call_program(ss.str(), output);
	if (code == 0) {
		BENCHMAX_LOG_INFO("benchmax.slurm", "Archived log files in " << p.filename_archive << " from " << p.tmp_dir);
	} else {
		BENCHMAX_LOG_WARN("benchmax.slurm", "Archiving of log files failed with exit code " << code);
		BENCHMAX_LOG_WARN("benchmax.slurm", output);
	}
}

std::vector<fs::path> collect_result_files(const fs::path& basedir) {
	BENCHMAX_LOG_DEBUG("benchmax.slurm", "Collecting results files from " << basedir);
	std::vector<fs::path> files;

	std::regex filenamere("JOB.[0-9]+_[0-9]+.(out|err)");
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
	std::string filename = p.tmp_dir + "/job-" + p.file_suffix + ".job";
	BENCHMAX_LOG_INFO("benchmax.slurm", "Generating submitfile " << filename);
	std::ofstream out(filename);
	out << "#!/usr/bin/env zsh" << std::endl;
	out << "### Job name" << std::endl;
	// Job name
	out << "#SBATCH --job-name=benchmax" << std::endl;
	// Output files (stdout and stderr)
	out << "#SBATCH -o " << p.tmp_dir << "/JOB.%A_%a.out" << std::endl;
	out << "#SBATCH -e " << p.tmp_dir << "/JOB.%A_%a.err" << std::endl;
	
	// Rough estimation of time in minutes (timeout * jobs)
	auto timeout = (std::chrono::seconds(p.limit_time) + std::chrono::seconds(p.grace_time));
	long minutes = std::chrono::duration_cast<std::chrono::minutes>(timeout * p.tasks / p.slices).count() * 2;
	minutes = std::min(minutes, static_cast<long>(60*24));

	out << "#SBATCH -t " << minutes << std::endl;
	// Memory usage in MB
	out << "#SBATCH --mem-per-cpu=" << p.limit_memory.mebi() + 1024 << "M" << std::endl;

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

	// Execute this slice
	out << "for i in `seq ${start} ${end}`; do" << std::endl;
	out << "\tcmd=$(time sed -n \"${i}p\" < " << p.filename_jobs << ")" << std::endl;
	out << "\techo \"Executing $cmd\"" << std::endl;
	out << "\techo \"# START ${i} #\"" << std::endl;
	out << "\techo \"# START ${i} #\" >&2" << std::endl;
	out << "\tstart=`date +\"%s%3N\"`" << std::endl;
	out << "\tulimit -c 0 && ulimit -S -v " << p.limit_memory.kibi() << " && ulimit -S -t " << std::chrono::seconds(timeout).count() << " && eval /usr/bin/time -v $cmd ; rc=$?" << std::endl;
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
	std::string filename = p.tmp_dir + "/job-" + p.file_suffix + ".job";
	BENCHMAX_LOG_INFO("benchmax.slurm", "Generating submitfile " << filename);
	std::ofstream out(filename);
	out << "#!/usr/bin/env zsh" << std::endl;
	out << "### Job name" << std::endl;
	// Job name
	out << "#SBATCH --job-name=benchmax" << std::endl;
	// Output files (stdout and stderr)
	out << "#SBATCH -o " << p.tmp_dir << "/JOB.%A_%a.out" << std::endl;
	out << "#SBATCH -e " << p.tmp_dir << "/JOB.%A_%a.err" << std::endl;
	
	// Rough estimation of time in minutes (timeout * slice_size)
	auto timeout = (std::chrono::seconds(p.limit_time) + std::chrono::seconds(p.grace_time));
	long minutes = std::chrono::duration_cast<std::chrono::minutes>(timeout * p.slice_size).count() * 2;
	minutes = std::min(minutes + 1, static_cast<long>(60*24));

	out << "#SBATCH -t " << minutes << std::endl;
	// Memory usage in MB
	out << "#SBATCH --mem-per-cpu=" << p.limit_memory.mebi() + 1024 << "M" << std::endl;

	// Load environment
	out << "source ~/load_environment" << std::endl;
	// Change current directory
	out << "cd " << p.tmp_dir << std::endl;

	// Calculate slices for jobfile
	out << "min=$SLURM_ARRAY_TASK_MIN" << std::endl;
	out << "max=$SLURM_ARRAY_TASK_MAX" << std::endl;
	out << "cur=$SLURM_ARRAY_TASK_ID" << std::endl;
	out << "slicesize=" << p.slice_size << std::endl;
	out << "start=$(( (cur - 1) * slicesize + 1 + " << p.job_range.first << " ))" << std::endl;
	out << "end=$(( start + slicesize - 1 + " << p.job_range.first << " ))" << std::endl;
	out << "end=$((end<" << p.job_range.second << " ? end : " << p.job_range.second << "))" << std::endl;

	// Execute this slice
	out << "for i in `seq ${start} ${end}`; do" << std::endl;
	out << "lineidx=$(( i - " << p.job_range.first << " ))" << std::endl;
	out << "\tcmd=$(time sed -n \"${lineidx}p\" < " << p.filename_jobs << ")" << std::endl;
	out << "\techo \"Executing $cmd\"" << std::endl;
	out << "\techo \"# START ${i} #\"" << std::endl;
	out << "\techo \"# START ${i} #\" >&2" << std::endl;
	out << "\tstart=`date +\"%s%3N\"`" << std::endl;
	// out << "\tulimit -c 0 && ulimit -S -v " << p.limit_memory.kibi() << " && ulimit -S -t " << std::chrono::seconds(timeout).count() << " && eval /usr/bin/time -v $cmd ; rc=$?" << std::endl;
	out << "\tulimit -c 0 && ulimit -S -v " << p.limit_memory.kibi() << " && eval /usr/bin/time -v timeout --signal=TERM --preserve-status " << std::chrono::seconds(timeout).count() << "s  $cmd ; rc=$?" << std::endl;
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

void clear_directory(const fs::path& basedir) {
	BENCHMAX_LOG_INFO("benchmax.slurm", "Clear directory " << basedir);
	for (const auto& entry : std::filesystem::directory_iterator(basedir)) {
		std::filesystem::remove_all(entry.path());
	}
	BENCHMAX_LOG_INFO("benchmax.slurm", "Cleared");
	// std::vector<fs::path> files;
	// std::regex filenamere("JOB.[0-9]+_[0-9]+.(out|err)");
	// for (const auto& f: fs::directory_iterator(basedir)) {
	// 	if (!std::regex_match(f.path().filename().string(), filenamere)) {
	// 		continue;
	// 	}
	// 	files.emplace_back(f.path());
	// }
	// for (const auto& f: files) {
	// 	std::filesystem::remove(f);
	// }
	// BENCHMAX_LOG_INFO("benchmax.slurm", "Cleared " << files.size() << " log files.");
}

bool is_job_finished(int jobid) {
	std::stringstream cmd;
	cmd << "sacct -o state  -j " << jobid;
	BENCHMAX_LOG_DEBUG("benchmax.slurm", "Command: " << cmd.str());
	std::string output;
	call_program(cmd.str(), output, false);
	
	std::istringstream iss(output);
	std::string line;
	std::getline(iss, line);
	assert(line.find("State") != std::string::npos);
	std::getline(iss, line);
	assert(line.find("----------") != std::string::npos);
	while (std::getline(iss, line)) {
		if (line.find("COMPLETED") == std::string::npos && line.find("CANCELLED") == std::string::npos && line.find("TIMEOUT") == std::string::npos) {
			return false;
		}
	}
	return true;
}

}
}