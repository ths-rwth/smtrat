#include "Settings.h"

namespace benchmax {
	
	bool Settings::UseStats;
	bool Settings::ProduceLatex;
	std::size_t Settings::memoryLimit;
	std::size_t Settings::timeLimit;
	std::string Settings::validationtoolpath;
	std::string Settings::outputDir;
	std::string Settings::WrongResultPath;
	std::string Settings::StatsXMLFile;
	std::string Settings::RemoteOutputDirectory;
	std::string Settings::PathOfBenchmarkTool;
	Tool* Settings::ValidationTool = nullptr;
	std::vector<Node*> Settings::Nodes;
	std::vector<std::string> Settings::pathes;
	std::vector<std::string> Settings::smtratapps;
	std::vector<std::string> Settings::z3apps;
	std::vector<std::string> Settings::isatapps;
	std::vector<std::string> Settings::redlog_rlqeapps;
	std::vector<std::string> Settings::redlog_rlcadapps;
	std::vector<std::string> Settings::qepcadapps;
	std::vector<std::string> Settings::nodes;
	std::vector<std::string> Settings::composeFiles;
	
	const std::string Settings::ExitMessage = "AllDone";
}
