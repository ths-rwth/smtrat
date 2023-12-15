#pragma once


#include <benchmax/benchmarks/benchmarks.h>
#include <benchmax/settings/Settings.h>
#include <benchmax/utils/filesystem.h>
#include <benchmax/backends/Jobs.h>

#include <fstream>
#include <map>
#include <string>

namespace benchmax {

/**
 * Writes results to a csv file.
 */
class CSVWriter {
private:
	std::ofstream mFile;

	void replace(std::string& s, const std::string& pattern, const std::string& replacement) const {
		std::size_t pos = 0;
		while ((pos = s.find(pattern, pos)) != std::string::npos) {
			s.replace(pos, pattern.length(), replacement);
			pos += replacement.length();
		}
	}
	std::string sanitize(const std::string& s, bool eliminateSlashes = false) const {
		std::string res(s);
		//replace(res, "<", "&lt;");
		//replace(res, ">", "&gt;");
		if (eliminateSlashes) replace(res, "/", ".");
		return res;
	}
	std::string sanitizeTool(const std::unique_ptr<Tool>& tool) const {
		return sanitize(remove_prefix(tool->binary(), settings_tools().tools_common_prefix), false);
	}
	std::string sanitizeFile(const fs::path& file) const {
		return sanitize(remove_prefix(file, settings_benchmarks().input_directories_common_prefix), false);
	}
	template<typename Results>
	std::vector<std::string> collectStatistics(const Jobs& jobs, const Results& results, Tool* tool) const {
		std::vector<std::string> res;
		for (const auto& filename: jobs.files()) { // for (const auto& run: results.data())
			const auto& run = results.get(tool, filename);
			run->get().restore();
			for (const auto& stat: run->get().additional) {
				res.emplace_back(stat.first);
			}
			run->get().store();
		}
		std::sort(res.begin(), res.end());
		res.erase(
			std::unique(res.begin(), res.end()),
			res.end()
		);
		return res;
	}
public:
	/// Open file for writing.
	CSVWriter(const std::string& filename): mFile(filename) {
	}

	/// Write results to file.
	template<typename Results>
	void write(const Jobs& jobs, const Results& results) {
		std::map<Tool*,std::vector<std::string>> tool_stats;
		{
			std::stringstream second_row;
			// mFile << ",";
			// second_row << ",";
			for (const auto& tool: jobs.tools()) {
				mFile << "," << sanitizeTool(tool) << "," << sanitizeTool(tool) << "," << sanitizeTool(tool);
				second_row << ",answer,exitcode,runtime";
				tool_stats.emplace(tool.get(), collectStatistics(jobs, results, tool.get()));
				for (const auto& s: tool_stats.at(tool.get())) {
					mFile << "," << sanitizeTool(tool);
					second_row << "," << sanitize(s);
				}
			}
			mFile << std::endl << second_row.rdbuf() << std::endl;
		}
		for (const auto& filename: jobs.files()) {
			mFile << "\"" << sanitizeFile(filename) << "\"";
			for (const auto& tool: jobs.tools()) {
				const auto& result = results.get(tool.get(), filename);
				if (!result) {
					mFile << ",,,";
					for (std::size_t i = 0; i < tool_stats.at(tool.get()).size(); i++) {
						mFile << ",";
					}
				} else {
					const auto& res = result->get();
					res.restore();
					mFile << "," << res.answer << "," << res.exitCode << "," << std::chrono::milliseconds(res.time).count();
					for (const auto& stat : tool_stats.at(tool.get())) {
						mFile << ",";
						if (res.additional.find(stat) != res.additional.end()) {
							mFile << "\"" << res.additional.at(stat) << "\"";
						}
					}
					res.forget();
				}
			}
			mFile << std::endl;
		}
	}
};

}
