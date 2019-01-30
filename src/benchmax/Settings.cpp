#include "../cli/config.h"
#ifdef __VS
#pragma warning(push, 0)
#include <boost/operators.hpp>
#pragma warning(pop)
#else
#include <boost/operators.hpp>
#endif

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
	std::string Settings::pathPrefix;
	std::chrono::seconds Settings::timeLimit;
	bool Settings::wallclock;
	std::size_t Settings::memoryLimit;
	std::string Settings::validationtoolpath;
	std::string Settings::WrongResultPath;
	std::string Settings::StatsXMLFile;
	std::string Settings::fileSuffix;
	
	std::vector<std::string> Settings::tools_generic;
	std::vector<std::string> Settings::tools_smtrat;
	std::vector<std::string> Settings::tools_smtrat_opb;
	std::vector<std::string> Settings::tools_minisatp;
	std::vector<std::string> Settings::tools_z3;
	std::string Settings::toolsPrefix;
	
	std::string Settings::RemoteOutputDirectory;
	std::string Settings::PathOfBenchmarkTool;
	boost::optional<Tool> Settings::ValidationTool;
	
	const std::string Settings::ExitMessage = "AllDone";
	std::time_t Settings::startTime;
}
