#include <boost/operators.hpp>

#include "Settings.h"

namespace benchmax {
	
	bool Settings::verbose;
    bool Settings::quiet;
    bool Settings::mute;
	
	bool Settings::ProduceLatex;
	bool Settings::UseStats;
	std::string Settings::outputDir;
	std::vector<std::string> Settings::composeFiles;
	
	std::string Settings::backend;
	
	std::vector<std::string> Settings::ssh_nodes;
	std::string Settings::ssh_basedir;
	std::string Settings::ssh_tmpdir;
	std::size_t Settings::ssh_maxchannels;
	
	std::vector<std::string> Settings::pathes;
	std::size_t Settings::timeLimit;
	std::size_t Settings::memoryLimit;
	std::string Settings::validationtoolpath;
	std::string Settings::WrongResultPath;
	std::string Settings::StatsXMLFile;
	std::string Settings::outputFile;
	
	std::vector<std::string> Settings::tools_smtrat;
	std::vector<std::string> Settings::tools_z3;
	std::vector<std::string> Settings::tools_isat;
	std::vector<std::string> Settings::tools_redlogrlqe;
	std::vector<std::string> Settings::tools_redlogrlcad;
	std::vector<std::string> Settings::tools_qepcad;
	
	std::string Settings::RemoteOutputDirectory;
	std::string Settings::PathOfBenchmarkTool;
	boost::optional<Tool> Settings::ValidationTool;
	
	const std::string Settings::ExitMessage = "AllDone";
	std::time_t Settings::startTime;
}
