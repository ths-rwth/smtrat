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
 * Writes results to a xml file.
 */
class XMLWriter {
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
		replace(res, "<", "&lt;");
		replace(res, ">", "&gt;");
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
	std::vector<std::string> collectStatistics(const Results& results) const {
		std::vector<std::string> res;
		for (const auto& run: results.data()) {
			for (const auto& stat: run.second.additional) {
				res.emplace_back(stat.first);
			}
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
	XMLWriter(const std::string& filename): mFile(filename) {
	}

	/// Write results to file.
	template<typename Results>
	void write(const Jobs& jobs, const Results& results) {
		mFile << "<?xml version=\"1.0\"?>" << std::endl;
		mFile << "<results>" << std::endl;
		mFile << "\t<solvers prefix=\"" << settings_tools().tools_common_prefix.native() << "\">" << std::endl;
		for (const auto& tool: jobs.tools()) {
			mFile << "\t\t<solver solver_id=\"" << sanitizeTool(tool) << "\" />" << std::endl;
		}
		mFile << "\t</solvers>" << std::endl;
		mFile << "\t<statistics>" << std::endl;
		for (const auto& s: collectStatistics(results)) {
			mFile << "\t\t<stat name=\"" << sanitize(s) << "\" />" << std::endl;
		}
		mFile << "\t</statistics>" << std::endl;
		
		mFile << "\t<benchmarks prefix=\"" << settings_benchmarks().input_directories_common_prefix.native() << "\">" << std::endl;
		for (const auto& filename: jobs.files()) {
			mFile << "\t\t<file name=\"" << sanitizeFile(filename) << "\">" << std::endl;
			for (const auto& tool: jobs.tools()) {
				const auto& result = results.get(tool.get(), filename);
				if (!result) continue;
				const auto& res = result->get();
				mFile << "\t\t\t<run solver_id=\"" << sanitizeTool(tool) << "\" timeout=\"" << std::chrono::seconds(settings_benchmarks().limit_time).count() << "s\">" << std::endl;
				if (!res.additional.empty()) {
					mFile << "\t\t\t\t<statistics>" << std::endl;
					for (const auto& stat: res.additional) {
						mFile << "\t\t\t\t\t<stat name=\"" << sanitize(stat.first) << "\">" << stat.second << "</stat>" << std::endl;
					}
					mFile << "\t\t\t\t</statistics>" << std::endl;
				}
				mFile << "\t\t\t\t<results>" << std::endl;
				mFile << "\t\t\t\t\t<result name=\"answer\" type=\"string\">" << res.answer << "</result>" << std::endl;
				mFile << "\t\t\t\t\t<result name=\"exitcode\" type=\"int\">" << res.exitCode << "</result>" << std::endl;
				mFile << "\t\t\t\t\t<result name=\"runtime\" type=\"msec\">" << std::chrono::milliseconds(res.time).count() << "</result>" << std::endl;
				mFile << "\t\t\t\t</results>" << std::endl;
				mFile << "\t\t\t</run>" << std::endl;
			}
			mFile << "\t\t</file>" << std::endl;
		}
		mFile << "\t</benchmarks>" << std::endl;
		mFile << "</results>" << std::endl;
	}
};

}
