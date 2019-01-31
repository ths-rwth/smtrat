#pragma once

#include "Backend.h"

#include "../logging.h"
#include "../utils/Execute.h"
#include "../utils/durations.h"

#include <boost/program_options.hpp>

#include <algorithm>
#include <filesystem>
#include <random>
#include <regex>

namespace benchmax {

struct SlurmBackendSettings {
	std::size_t slices;
	std::string tmp_dir;
	bool keep_logs;
	std::string archive_log_file;
};

template<typename T>
void registerSlurmBackendSettings(T& parser) {
	namespace po = boost::program_options;
	auto& settings = settings::Settings::getInstance();
	auto& s = settings.add<SlurmBackendSettings>("backend-slurm");
	
	parser.add("Slurm Backend settings", s).add_options()
		("slurm:slices", po::value<std::size_t>(&s.slices)->default_value(1000), "Number of slices for array job")
		("slurm:tmp-dir", po::value<std::string>(&s.tmp_dir)->default_value("/tmp/"), "temporary directory")
		("slurm:keep-logs", po::bool_switch(&s.keep_logs), "Do not delete log files")
		("slurm:archive-logs", po::value<std::string>(&s.archive_log_file)->value_name("filename"), "Store log files in this tgz archive")
	;
}

inline const auto& settings_slurm() {
	static const auto& s = settings::Settings::getInstance().get<SlurmBackendSettings>("backend-slurm");
	return s;
}

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

	std::vector<std::filesystem::path> collect_result_files(const fs::path& basedir, int jobid) const {
		BENCHMAX_LOG_DEBUG("benchmax.slurm", "Collecting results files from " << basedir);
		std::vector<std::filesystem::path> files;

		std::regex filenamere("JOB." + std::to_string(jobid) + "_[0-9]+.(out|err)");
		for (const auto& f: std::filesystem::directory_iterator(basedir)) {
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

	std::string generateSubmitFile(const std::string& jobfile, std::size_t num_input) {
		std::string filename = "job-" + std::to_string(settings_core().start_time) + ".job";
		BENCHMAX_LOG_DEBUG("benchmax.slurm", "Writing submit file to " << filename);
		std::ofstream out(settings_slurm().tmp_dir + "/" + filename);
		out << "#!/usr/bin/env zsh" << std::endl;
		out << "### Job name" << std::endl;
		// Job name
		out << "#SBATCH --job-name=benchmax" << std::endl;
		// Output files (stdout and stderr)
		out << "#SBATCH -o " << settings_slurm().tmp_dir << "/JOB.%A_%a.out" << std::endl;
		out << "#SBATCH -e " << settings_slurm().tmp_dir << "/JOB.%A_%a.err" << std::endl;
		// Rough estimation of time in minutes (timeout * jobs)
		out << "#SBATCH -t " << (static_cast<std::size_t>(seconds(settings_benchmarks().limit_time).count()) * num_input / 60 + 1) << std::endl;
		// Memory usage in MB
		out << "#SBATCH --mem-per-cpu=" << (settings_benchmarks().limit_memory + 1024) << "M" << std::endl;

		// Load environment
		out << "source ~/load_environment" << std::endl;
		// Change current directory
		out << "cd " << settings_slurm().tmp_dir << std::endl;

		// Calculate slices for jobfile
		out << "min=$SLURM_ARRAY_TASK_MIN" << std::endl;
		out << "max=$SLURM_ARRAY_TASK_MAX" << std::endl;
		out << "cur=$SLURM_ARRAY_TASK_ID" << std::endl;
		out << "tasks=" << num_input << std::endl;
		out << "jobcount=$(( max - min + 1 ))" << std::endl;
		out << "slicesize=$(( (tasks + jobcount + 1) / jobcount ))" << std::endl;
		out << "start=$(( (cur - 1) * slicesize + min ))" << std::endl;
		out << "end=$(( start + slicesize - 1 ))" << std::endl;

		auto timeout = (seconds(settings_benchmarks().limit_time) + std::chrono::seconds(3)).count();
		// Execute this slice
		out << "for i in `seq ${start} ${end}`; do" << std::endl;
		out << "\tcmd=$(sed -n \"${i}p\" < " << jobfile << ")" << std::endl;
		out << "\techo \"Executing $cmd\"" << std::endl;
		out << "\techo \"# START ${i} #\"" << std::endl;
		out << "\techo \"# START ${i} #\" >&2" << std::endl;
		out << "\tstart=`date +\"%s%3N\"`" << std::endl;
		out << "\tulimit -S -v " << (settings_benchmarks().limit_memory * 1024) << " && ulimit -S -t " << timeout << " && $cmd ; rc=$?" << std::endl;
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
	void run(const Tools& tools, const std::vector<BenchmarkSet>& benchmarks) {

		std::string jobsfile = "jobs-" + std::to_string(settings_core().start_time) + ".jobs";
		for (const auto& tool: tools) {
			for (const BenchmarkSet& set: benchmarks) {
				for (const auto& file: set) {
					mResults.emplace_back(JobData { tool.get(), file, set.baseDir(), BenchmarkResult() });
				}
			}
		}
		BENCHMAX_LOG_DEBUG("benchmax.slurm", "Gathered " << mResults.size() << " jobs");
		shuffle_jobs();
		BENCHMAX_LOG_INFO("benchmax.slurm", "Writing job file to " << jobsfile);
		std::ofstream jobs(settings_slurm().tmp_dir + "/" + jobsfile);
		for (const auto& r: mResults) {
			jobs << std::get<0>(r)->getCommandline(std::get<2>(r)) << std::endl;
		}
		jobs.close();
		auto submitfile = generateSubmitFile(settings_slurm().tmp_dir + "/" + jobsfile, mResults.size());

		BENCHMAX_LOG_INFO("benchmax.slurm", "Submitting job now.");
		std::string output;
		callProgram("sbatch --wait --array=1-" + std::to_string(settings_slurm().slices) + " -N1 " + settings_slurm().tmp_dir + "/" + submitfile, output, true);
		BENCHMAX_LOG_INFO("benchmax.slurm", "Job terminated, collecting results.");
		int jobid = getJobID(output);

		auto files = collect_result_files(settings_slurm().tmp_dir, jobid);
		for (const auto& f: files) {
			parse_result_file(f);
		}
		BENCHMAX_LOG_DEBUG("benchmax.slurm", "Parsed results.");
		for (auto& r: mResults) {
			addResult(std::get<0>(r), std::get<1>(r), std::get<2>(r), std::get<3>(r));
		}

		if (settings_slurm().archive_log_file != "") {
			std::string output;
			std::stringstream ss;
			ss << "tar -czf " << settings_slurm().archive_log_file << " ";
			ss << "-C " << settings_slurm().tmp_dir << " ";
			ss << jobsfile << " " << submitfile << " ";
			ss << "JOB." << jobid << "_*";
			int code = callProgram(ss.str(), output);
			if (code == 0) {
				BENCHMAX_LOG_INFO("benchmax.slurm", "Archived log files in " << settings_slurm().archive_log_file);
			} else {
				BENCHMAX_LOG_WARN("benchmax.slurm", "Archiving of log files failed with exit code " << code);
				BENCHMAX_LOG_WARN("benchmax.slurm", output);
			}
		}
		if (!settings_slurm().keep_logs) {
			BENCHMAX_LOG_INFO("benchmax.slurm", "Removing log files.");
			for (const auto& f: files) {
				std::filesystem::remove(f);
			}
		}

		BENCHMAX_LOG_INFO("benchmax.slurm", "Finished.");
	}
};

}