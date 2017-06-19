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
#ifdef __VS
#pragma warning(push, 0)
#include <boost/optional.hpp>
#include <boost/program_options.hpp>
#pragma warning(pop)
#else
#include <boost/optional.hpp>
#include <boost/program_options.hpp>
#endif

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
			("verbose,v", po::bool_switch(&verbose)->default_value(false), "display comprehensive output")
			("quiet", po::bool_switch(&quiet)->default_value(false), "display only final output")
			("mute", po::bool_switch(&mute)->default_value(false), "prevent all output except for possible LaTeX output")
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
		backendOptions.add_options()
			("backend,b", po::value<std::string>(&backend), "Backend to be used. Possible values: \"condor\", \"local\", \"ssh\".")
		;
		backendOptions_SSH.add_options()
			("node,N", po::value<std::vector<std::string>>(&ssh_nodes), "remote blades")
            ("channels", po::value<std::size_t>(&ssh_maxchannels)->default_value(4), "channels per connection")
            ("basedir", po::value<std::string>(&ssh_basedir)->default_value("~/"), "remote base directory")
            ("tmpdir", po::value<std::string>(&ssh_tmpdir)->default_value("/tmp/"), "remote temporary directory")
		;
		backendOptions.add(backendOptions_SSH);
		
		benchmarkOptions.add_options()
			("include-directory,D", po::value<std::vector<std::string>>(&pathes), "path to look for benchmarks (several are possible)")
			("timeout,T", po::value<std::size_t>()->default_value(60), "timeout for all competing solvers in seconds")
			("wallclock", po::value<bool>(&wallclock)->default_value(false), "Use wall clock for timeout")
			("memory,M", po::value<std::size_t>(&memoryLimit)->default_value(1024), "memory limit for all competing solvers in mega bytes")
			("validation,V", po::value<std::string>(&validationtoolpath), "tool to check assumptions")
			("wrong-result-path,W", po::value<std::string>(&WrongResultPath)->default_value("wrong_result/"), "path to the directory to store the wrong results")
			("stats-xml-file,X", po::value<std::string>(&StatsXMLFile)->default_value("stats.xml"), "path to the xml-file where the statistics are stored")
			("output-file,f", po::value<std::string>(&outputFile), "output file")
		;
		solverOptions.add_options()
			("tool", po::value<std::vector<std::string>>(&tools_generic), "any tool")
			("smtrat,S", po::value<std::vector<std::string>>(&tools_smtrat), "an SMT-LIB 2.0 solver with SMT-RAT interface (multiple are possible)")
			("smtrat-opb,O", po::value<std::vector<std::string>>(&tools_smtrat_opb), "SMT-RAT with OPB interface")
			("minisatp", po::value<std::vector<std::string>>(&tools_minisatp), "Minisatp with OPB interface")
			("z3,Z", po::value<std::vector<std::string>>(&tools_z3), "an SMT-LIB 2.0 solver with z3 interface (multiple are possible)")
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
		WrongResultPath = outputDir + WrongResultPath;
		RemoteOutputDirectory = "/scratch/";
		if (validationtoolpath != "") {
			//ValidationTool.emplace(createTool(benchmax::TI_Z3, validationtoolpath));
		}
		
		timeLimit = std::chrono::seconds(vm["timeout"].as<std::size_t>());
		pathPrefix = commonPrefix(pathes);
		std::cout << "Common path prefix is " << pathPrefix << std::endl;
		toolsPrefix = commonPrefix({tools_generic, tools_smtrat, tools_smtrat_opb, tools_minisatp, tools_z3});
		std::cout << "Common tools prefix is " << toolsPrefix << std::endl;
	}
	
	bool has(const std::string& s) const {
		return vm.count(s);
	}
	template<typename T>
	const T& as(const std::string& s) const {
		return vm[s].as<T>();
	}

	/// Core Options
	static bool verbose;
    static bool quiet;
    static bool mute;
    
    /// Tool Options
	static bool ProduceLatex;
	static bool UseStats;
	static std::string outputDir;
	static std::vector<std::string> composeFiles;
    
    /// Backend Options
	static std::string backend;
    
    /// SSH Backend Options
	static std::vector<std::string> ssh_nodes;
    static std::string ssh_basedir;
    static std::string ssh_tmpdir;
    static std::size_t ssh_maxchannels;
    
    /// Benchmark Options
	static std::vector<std::string> pathes;
	static std::string pathPrefix;
	static std::chrono::seconds timeLimit;
	static bool wallclock;
	static std::size_t memoryLimit;
	static std::string validationtoolpath;
	static std::string WrongResultPath;
	static std::string StatsXMLFile;
	static std::string outputFile;
    
    /// Solver Options
	static std::vector<std::string> tools_generic;
	static std::vector<std::string> tools_smtrat;
	static std::vector<std::string> tools_smtrat_opb;
	static std::vector<std::string> tools_minisatp;
	static std::vector<std::string> tools_z3;
	static std::string toolsPrefix;
    
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
