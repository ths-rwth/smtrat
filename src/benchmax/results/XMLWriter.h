#pragma once


#include "../settings/Settings.h"
#include "../benchmarks/benchmarks.h"
#include "../utils/strings.h"

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
	std::string sanitizeTool(const Tool* tool) const {
		return sanitize(remove_prefix(tool->binary().native(), settings_tools().tools_common_prefix), true);
	}
	std::string sanitizeFile(const fs::path& file, const std::string& prefix) const {
		return sanitize(remove_prefix(file.native(), prefix), true);
	}
	template<typename Results>
	std::vector<std::string> collectStatistics(const Results& results) const {
		std::vector<std::string> res;
		for (const auto& rfile: results) {
			for (const auto& run: rfile.second.data) {
				for (const auto& stat: run.second.additional) {
					res.emplace_back(stat.first);
				}
			}
			std::sort(res.begin(), res.end());
			res.erase(
				std::unique(res.begin(), res.end()),
				res.end()
			);
		}
		return res;
	}
public:
	/// Open file for writing.
	XMLWriter(const std::string& filename): mFile(filename) {
	}

	/// Write results to file.
	template<typename Results>
	void write(const std::map<const Tool*, std::size_t>& tools, const Results& results) {
		mFile << "<?xml version=\"1.0\"?>" << std::endl;
		mFile << "<benchmarksets>" << std::endl;
		mFile << "\t<solvers>" << std::endl;
		std::set<std::string> toolNames;
		for (const auto& tool: tools) toolNames.insert(sanitizeTool(tool.first));
		for (const auto& tool: toolNames) {
			mFile << "\t\t<solver solver_id=\"" << tool << "\" />" << std::endl;
		}
		mFile << "\t</solvers>" << std::endl;
		mFile << "\t<statistics>" << std::endl;
		for (const auto& s: collectStatistics(results)) {
			mFile << "\t\t<stat name=\"" << sanitize(s) << "\" />" << std::endl;
		}
		mFile << "\t</statistics>" << std::endl;
		
		
		for (const auto& res: results) {
			fs::path setBaseDir = res.first;
			mFile << "\t<benchmarkset name=\"" << sanitizeFile(setBaseDir, settings_benchmarks().input_directories_common_prefix) << "\">" << std::endl;
			for (const auto& file: res.second.files) {
				fs::path filename = file.first;
				mFile << "\t\t<benchmarkfile name=\"" << sanitizeFile(filename, setBaseDir.native()) << "\">" << std::endl;
				for (const auto& tool: tools) {
					std::pair<std::size_t, std::size_t> resultID(tool.second, file.second);
					auto it = res.second.data.find(resultID);
					if (it == res.second.data.end()) continue;
					mFile << "\t\t\t<run solver_id=\"" << sanitizeTool(tool.first) << "\" timeout=\"" << std::chrono::seconds(settings_benchmarks().limit_time).count() << "s\">" << std::endl;
					if (!it->second.additional.empty()) {
						mFile << "\t\t\t\t<statistics>" << std::endl;
						for (const auto& stat: it->second.additional) {
							mFile << "\t\t\t\t\t<stat name=\"" << sanitize(stat.first) << "\">" << stat.second << "</stat>" << std::endl;
						}
						mFile << "\t\t\t\t</statistics>" << std::endl;
					}
					mFile << "\t\t\t\t<results>" << std::endl;
					mFile << "\t\t\t\t\t<result name=\"answer\" type=\"string\">" << it->second.answer << "</result>" << std::endl;
					mFile << "\t\t\t\t\t<result name=\"exitcode\" type=\"int\">" << it->second.exitCode << "</result>" << std::endl;
					mFile << "\t\t\t\t\t<result name=\"runtime\" type=\"msec\">" << std::chrono::milliseconds(it->second.time).count() << "</result>" << std::endl;
					mFile << "\t\t\t\t</results>" << std::endl;
					mFile << "\t\t\t</run>" << std::endl;
				}
				mFile << "\t\t</benchmarkfile>" << std::endl;
			}
			mFile << "\t</benchmarkset>" << std::endl;
		}
		mFile << "</benchmarksets>" << std::endl;
	}
};

}
