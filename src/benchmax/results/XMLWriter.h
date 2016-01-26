#pragma once

#include <fstream>
#include <map>

namespace benchmax {

class XMLWriter {
private:
	std::ofstream mFile;
public:
	XMLWriter(const std::string& filename): mFile(filename) {
		mFile << "<?xml version=\"1.0\"?>" << std::endl;
		mFile << "<benchmarksets>" << std::endl;
	}
	
	void write(const std::map<Tool, std::size_t>& tools, const std::map<fs::path, std::size_t>& files, const std::map<std::pair<std::size_t,std::size_t>, BenchmarkResults>& results) {
		mFile << "\t<solvers>" << std::endl;
		for (const auto& tool: tools) {
			mFile << "\t\t<solver solver_id=\"" << tool.first.name() << "\" />" << std::endl;
		}
		mFile << "\t</solvers>" << std::endl;
		
		mFile << "\t<benchmarkset name=\"all\">" << std::endl;
		for (const auto& file: files) {
			mFile << "\t\t<benchmarkfile name=\"" << file.first.native() << "\">" << std::endl;
			for (const auto& tool: tools) {
				std::pair<std::size_t, std::size_t> resultID(tool.second, file.second);
				auto it = results.find(resultID);
				if (it == results.end()) continue;
				mFile << "\t\t\t<run solver_id=\"" << tool.first.name() << "\" timeout=\"" << Settings::timeLimit << "\">" << std::endl;
				mFile << "\t\t\t\t<results>" << std::endl;
				mFile << "\t\t\t\t<result name=\"runtime\" type=\"msec\">" << it->second.time << "</result>" << std::endl;
				mFile << "\t\t\t\t<result name=\"answer\" type=\"\">";
				switch (it->second.exitCode) {
					case 2: mFile << "sat"; break;
					case 3: mFile << "unsat"; break;
					case 4: mFile << "unknown"; break;
					case 5: mFile << "error"; break;
					case 11: mFile << "timeout"; break;
					case 12: mFile << "memout"; break;
					default: mFile << "segfault";
				}
				mFile << "</result>" << std::endl;
				mFile << "\t\t\t\t</results>" << std::endl;
				mFile << "\t\t\t</run>" << std::endl;
			}
			mFile << "\t\t</benchmarkfile>" << std::endl;
		}
		mFile << "\t</benchmarkset>" << std::endl;
	}
	
	~XMLWriter() {
		mFile << "<benchmarksets>" << std::endl;
		mFile.close();
	}
};
	
}
