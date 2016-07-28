#pragma once

#include <fstream>
#include <map>
#include <string>
#include "../utils/durations.h"

namespace benchmax {

class XMLWriter {
private:
	std::ofstream mFile;
	
	struct Filename: public fs::path {
		static std::string removeDanglingSlashes(const std::string& s) {
			std::string res = s;
			if (res.front() == '/') res = res.substr(1);
			if (res.back() == '/') res = res.substr(0, res.length() - 1);
			return res;
		}
		Filename(const fs::path& p): fs::path(p) {}
		std::string filename() const {
			return removeDanglingSlashes(fs::path::filename().native());
		}
		std::string removePrefix(const fs::path& baseDir) const {
			std::string prefix = baseDir.native();
			assert(prefix == native().substr(0, prefix.length()));
			return removeDanglingSlashes(native().substr(prefix.length()));
		}
	};

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
public:
	XMLWriter(const std::string& filename): mFile(filename) {
		mFile << "<?xml version=\"1.0\"?>" << std::endl;
		mFile << "<benchmarksets>" << std::endl;
	}

	template<typename Results>
	void write(const std::map<const Tool*, std::size_t>& tools, const Results& results) {
		mFile << "\t<solvers>" << std::endl;
		std::set<std::string> toolNames;
		for (const auto& tool: tools) toolNames.insert(sanitize(Filename(tool.first->binary()).filename(), true));
		for (const auto& tool: toolNames) {
			mFile << "\t\t<solver solver_id=\"" << tool << "\" />" << std::endl;
		}
		mFile << "\t</solvers>" << std::endl;
		
		for (const auto& res: results) {
			Filename setDir = res.first;
			mFile << "\t<benchmarkset name=\"" << sanitize(setDir.removePrefix(Settings::pathPrefix), true) << "\">" << std::endl;
			for (const auto& file: res.second.files) {
				Filename filename = file.first;
				mFile << "\t\t<benchmarkfile name=\"" << sanitize(filename.removePrefix(setDir)) << "\">" << std::endl;
				for (const auto& tool: tools) {
					std::pair<std::size_t, std::size_t> resultID(tool.second, file.second);
					auto it = res.second.data.find(resultID);
					if (it == res.second.data.end()) continue;
					mFile << "\t\t\t<run solver_id=\"" << sanitize(Filename(tool.first->binary()).filename(), true) << "\" timeout=\"" << seconds(Settings::timeLimit).count() << "s\">" << std::endl;
					if (!it->second.additional.empty()) {
						mFile << "\t\t\t\t<runtimestats>" << std::endl;
						mFile << "\t\t\t\t\t<module name=\"All\">" << std::endl;
						for (const auto& stat: it->second.additional) {
							mFile << "\t\t\t\t\t\t<stat name=\"" << sanitize(stat.first) << "\" value=\"" << stat.second << "\" />" << std::endl;
						}
						mFile << "\t\t\t\t\t</module>" << std::endl;
						mFile << "\t\t\t\t</runtimestats>" << std::endl;
					}
					mFile << "\t\t\t\t<results>" << std::endl;
					mFile << "\t\t\t\t\t<result name=\"runtime\" type=\"msec\">" << milliseconds(it->second.time).count() << "</result>" << std::endl;
					mFile << "\t\t\t\t\t<result name=\"exitcode\" type=\"int\">" << it->second.exitCode << "</result>" << std::endl;
					mFile << "\t\t\t\t\t<result name=\"answer\" type=\"\">" << it->second.status << "</result>" << std::endl;
					mFile << "\t\t\t\t</results>" << std::endl;
					mFile << "\t\t\t</run>" << std::endl;
				}
				mFile << "\t\t</benchmarkfile>" << std::endl;
			}
			mFile << "\t</benchmarkset>" << std::endl;
		}
	}

	~XMLWriter() {
		mFile << "</benchmarksets>" << std::endl;
		mFile.close();
	}
};

}
