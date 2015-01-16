/**
 * @file Settings.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <fstream>
#include <memory>
#include <boost/optional.hpp>
#include <boost/program_options.hpp>

#include "Tool.h"

namespace benchmax {

class Node;

namespace po = boost:: program_options;

class Settings {
private:
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
		coreOptions("Core options"),
		toolOptions("Tool options"),
		backendOptions("Backend options"),
		backendOptions_SSH("SSH backend options (if backend = \"SSH\")"),
		benchmarkOptions("Benchmark options"),
		solverOptions("Solver options")
	{
		coreOptions.add_options()
			("help,h", "show this help text")
			("verbose,v", po::bool_switch(&verbose), "display comprehensive output")
			("quiet", po::bool_switch(&quiet), "display only final output")
			("mute", po::bool_switch(&mute), "prevent all output except for possible LaTeX output")
			("copyright", "show the copyright")
			("disclaimer", "show the warranty disclaimer")
		;
		toolOptions.add_options()
			("latex,l", po::bool_switch(&ProduceLatex), "output a LaTeX table with all results at the end")
			("stats,s", po::bool_switch(&UseStats), "run solver with statistics")
			("output-dir,o", po::value<std::string>(&outputDir), "output directory")
			("compose,c", po::value<std::vector<std::string> >(&composeFiles), "Compose a list of stats files together")
		;
		backendOptions.add_options()
			("backend,b", po::value<std::string>(&backend), "Backend to be used. Possible values: \"condor\", \"local\", \"ssh\".")
		;
		backendOptions_SSH.add_options()
			("node,N", po::value<std::vector<std::string>>(&nodes), "remote blades")
		;
		backendOptions.add(backendOptions_SSH);
		
		benchmarkOptions.add_options()
			("include-directory,D", po::value<std::vector<std::string>>(&pathes), "path to look for benchmarks (several are possible)")
			("timeout,T", po::value<std::size_t>(&timeLimit)->default_value(150), "timeout for all competing solvers in seconds (standard: 150 sec)")
			("memory,M", po::value<std::size_t>(&memoryLimit)->default_value(1024), "memory limit for all competing solvers in mega bytes (standard: 1024 MB)")
			("validation,V", po::value<std::string>(&validationtoolpath), "tool to check assumptions")
			("wrong-result-path,W", po::value<std::string>(&WrongResultPath)->default_value("wrong_result/"), "path to the directory to store the wrong results")
			("stats-xml-file,X", po::value<std::string>(&StatsXMLFile)->default_value("stats.xml"), "path to the xml-file where the statistics are stored")
			("output-file,f", po::value<std::string>(&outputFile), "output file")
		;
		solverOptions.add_options()
			("smtrat,S", po::value<std::vector<std::string>>(&smtratapps), "an SMT-LIB 2.0 solver with SMT-RAT interface (multiple are possible)")
			("z3,Z", po::value<std::vector<std::string>>(&z3apps), "an SMT-LIB 2.0 solver with z3 interface (multiple are possible)")
			("isat,I", po::value<std::vector<std::string>>(&isatapps), "an .Hys solver with isat interface (multiple are possible)")
			("redlog_rlqe,R", po::value<std::vector<std::string>>(&redlog_rlqeapps), "Redlog solvers calling rlqe")
			("redlog_rlcad,C", po::value<std::vector<std::string>>(&redlog_rlcadapps), "Redlog solvers calling rlcad")
			("qepcad,Q", po::value<std::vector<std::string>>(&qepcadapps), "the tool QEPCAD B")
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
			ValidationTool.emplace(createTool(benchmax::TI_Z3, validationtoolpath));
		}
	}
	
	bool has(const std::string& s) const {
		return vm.count(s);
	}

	// Options
	bool verbose = false;
	bool quiet = false;
	bool mute = false;
	static bool ProduceLatex;
	static bool UseStats;
	static std::size_t memoryLimit;
	static std::size_t timeLimit;
	static std::string backend;
	static std::string validationtoolpath;
	static std::string outputDir;
	static std::string WrongResultPath;
	static std::string StatsXMLFile;
	static std::string RemoteOutputDirectory;
	static std::string PathOfBenchmarkTool;
	static std::string outputFile;
	static boost::optional<Tool> ValidationTool;
	static std::vector<std::string> pathes;
	static std::vector<std::string> smtratapps;
	static std::vector<std::string> z3apps;
	static std::vector<std::string> isatapps;
	static std::vector<std::string> redlog_rlqeapps;
	static std::vector<std::string> redlog_rlcadapps;
	static std::vector<std::string> qepcadapps;
	static std::vector<std::string> nodes;
	static std::vector<std::string> composeFiles;
	
	// Constants
	static const std::string ExitMessage;
	
	friend std::ostream& operator<<(std::ostream& os, const Settings& s) {
		os << s.desc_cmdline << std::endl;
		return os;
	}
};

}