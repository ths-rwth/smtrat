/**
 * @file Settings.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <chrono>
#include <ctime>
#include <fstream>
#include <memory>
#include "../cli/config.h"
#include <any>
#include <boost/optional.hpp>
#include <boost/program_options.hpp>
#include <carl/util/Singleton.h>

#include "tools/Tool.h"
#include "utils/strings.h"

namespace benchmax {

class Node;

namespace po = boost:: program_options;

class Settings {
private:
    unsigned printWidth;
    po::variables_map vm;
	po::options_description coreOptions;
	po::options_description toolOptions;
	po::options_description backendOptions;
	po::options_description backendOptions_SSH;
	po::options_description benchmarkOptions;
	po::options_description solverOptions;
	
	po::options_description desc_cmdline;
	po::options_description desc_file;
public:
	Settings(int argc, char** argv):
        printWidth(120),
		coreOptions("Core options", printWidth),
		toolOptions("Tool options", printWidth),
		backendOptions("Backend options", printWidth),
		backendOptions_SSH("SSH backend options (if backend = \"SSH\")", printWidth),
		benchmarkOptions("Benchmark options", printWidth),
		solverOptions("Solver options", printWidth)
	{
        startTime = std::time(nullptr);
		coreOptions.add_options()
			("help,h", "show this help text")
			//("verbose,v", po::bool_switch(&verbose)->default_value(false), "display comprehensive output")
			//("quiet", po::bool_switch(&quiet)->default_value(false), "display only final output")
			//("mute", po::bool_switch(&mute)->default_value(false), "prevent all output except for possible LaTeX output")
			("copyright", "show the copyright")
			("disclaimer", "show the warranty disclaimer")
		;
		toolOptions.add_options()
			("latex,l", po::bool_switch(&ProduceLatex), "output a LaTeX table with all results at the end")
			("stats,s", po::bool_switch(&UseStats), "run solver with statistics")
			("output-dir,o", po::value<std::string>(&outputDir), "output directory")
			("compose,c", po::value<std::vector<std::string> >(&composeFiles), "Compose a list of stats files together")
			("convert", po::value<std::string>(), "Convert a XML result file to .ods")
			("convert-filter", po::value<std::string>()->default_value("Benchmax"), "XSLT filter name to import XML file into libreoffice")
		;
		// commandline options
		desc_cmdline.add(coreOptions).add(toolOptions).add(backendOptions).add(benchmarkOptions).add(solverOptions);

		// external file
		desc_file.add(coreOptions).add(toolOptions).add(backendOptions).add(benchmarkOptions).add(solverOptions);
		
		// parse variables
		po::store(po::parse_command_line(argc, argv, desc_cmdline), vm);
		std::ifstream inifile("settings.ini");
		po::store(po::parse_config_file(inifile, desc_file), vm);

		po::notify(vm);
		RemoteOutputDirectory = "/scratch/";
	}
	
	bool has(const std::string& s) const {
		return vm.count(s);
	}
	template<typename T>
	const T& as(const std::string& s) const {
		return vm[s].as<T>();
	}

	/// Core Options
	//static bool verbose;
    //static bool quiet;
    //static bool mute;
    
    /// Tool Options
	static bool ProduceLatex;
	static bool UseStats;
	static std::string outputDir;
	static std::vector<std::string> composeFiles;
    
    /// Backend Options
	//static std::string backend;
    
    /// SSH Backend Options
	//static std::vector<std::string> ssh_nodes;
    //static std::string ssh_basedir;
    //static std::string ssh_tmpdir;
    //static std::size_t ssh_maxchannels;
    
    /// Benchmark Options
	//static std::vector<std::string> pathes;
	//static std::string pathPrefix;
	//static std::chrono::seconds timeLimit;
	//static bool wallclock;
	//static std::size_t memoryLimit;
	//static std::string validationtoolpath;
	//static std::string WrongResultPath;
	//static std::string StatsXMLFile;
	//static std::string fileSuffix;
    
    /// Solver Options
	//static std::vector<std::string> tools_generic;
	//static std::vector<std::string> tools_smtrat;
	//static std::vector<std::string> tools_smtrat_opb;
	//static std::vector<std::string> tools_minisatp;
	//static std::vector<std::string> tools_z3;
	//static std::string toolsPrefix;
    
	static std::string RemoteOutputDirectory;
	static std::string PathOfBenchmarkTool;
	static boost::optional<Tool> ValidationTool;
	
	// Constants
	static const std::string ExitMessage;
    static std::time_t startTime;
	
	friend std::ostream& operator<<(std::ostream& os, const Settings& s) {
		os << s.desc_cmdline << std::endl;
		return os;
	}
};

}
