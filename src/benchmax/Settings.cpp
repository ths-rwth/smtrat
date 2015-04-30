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
	
	bool Settings::UseStats;
	bool Settings::ProduceLatex;
	std::size_t Settings::memoryLimit;
	std::size_t Settings::timeLimit;
	std::string Settings::backend;
	std::string Settings::validationtoolpath;
	std::string Settings::outputDir;
	std::string Settings::WrongResultPath;
	std::string Settings::StatsXMLFile;
	std::string Settings::RemoteOutputDirectory;
	std::string Settings::PathOfBenchmarkTool;
	std::string Settings::outputFile;
	boost::optional<Tool> Settings::ValidationTool;
	std::vector<std::string> Settings::pathes;
	std::vector<std::string> Settings::tools_smtrat;
	std::vector<std::string> Settings::tools_z3;
	std::vector<std::string> Settings::tools_isat;
	std::vector<std::string> Settings::tools_redlogrlqe;
	std::vector<std::string> Settings::tools_redlogrlcad;
	std::vector<std::string> Settings::tools_qepcad;
	std::vector<std::string> Settings::nodes;
	std::vector<std::string> Settings::composeFiles;
	
	const std::string Settings::ExitMessage = "AllDone";
}
