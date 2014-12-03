/**
 * @file Settings.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <boost/program_options.hpp>

namespace benchmax {

namespace po = boost:: program_options;

class Settings {
private:
    po::variables_map vm;
	po::options_description coreOptions;
	po::options_description toolOptions;
	po::options_description benchmarkOptions;
	po::options_description solverOptions;
	po::options_description desc_cmdline;
	po::options_description desc_file;
public:
	Settings(int argc, char** argv):
		coreOptions("Core options"),
		toolOptions("Tool options"),
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
			("latex,l", po::bool_switch(&BenchmarkTool::ProduceLatex), "output a LaTeX table with all results at the end")
			("stats,s", po::bool_switch(&BenchmarkTool::UseStats), "run solver with statistics")
			("output-dir,o", po::value<string>(&outputDir), "output directory")
			("compose,c", po::value<std::vector<string> >(&composeFiles), "Compose a list of stats files together")
		;
		
		benchmarkOptions.add_options()
			("include-directory,D", po::value<vector<string> >(&pathes), "path to look for benchmarks (several are possible)")
			("timeout,T", po::value<unsigned>(&BenchmarkTool::Timeout), "timeout for all competing solvers in seconds (standard: 150 sec)")
			("memory,M", po::value<unsigned>(&BenchmarkTool::Memout), "memory limit for all competing solvers in mega bytes (standard: 1000 MB)")
			("validation,V", po::value<string>(&validationtool), "tool to check assumptions")
			("wrong-result-path,W", po::value<string>(&wrongResultsDir), "path to the directory to store the wrong results")
			("node,N", po::value<vector<string> >(&nodes), "remote blades")
			("stats-xml-file,X", po::value<string>(&statsXMLFile), "path to the xml-file where the statistics are stored")
		;
		solverOptions.add_options()
			("smtrat,S", po::value<vector<string> >(&smtratapps), "an SMT-LIB 2.0 solver with SMT-RAT interface (multiple are possible)")
			("z3,Z", po::value<vector<string> >(&z3apps), "an SMT-LIB 2.0 solver with z3 interface (multiple are possible)")
			("isat,I", po::value<vector<string> >(&isatapps), "an .Hys solver with isat interface (multiple are possible)")
			("redlog_rlqe,R", po::value<vector<string> >(&redlog_rlqeapps), "Redlog solvers calling rlqe")
			("redlog_rlcad,C", po::value<vector<string> >(&redlog_rlcadapps), "Redlog solvers calling rlcad")
			("qepcad,Q", po::value<vector<string> >(&qepcadapps), "the tool QEPCAD B")
		;
		// commandline options
		desc_cmdline.add(coreOptions).add(toolOptions).add(benchmarkOptions).add(solverOptions);

		// external file
		desc_file.add(coreOptions).add(toolOptions).add(benchmarkOptions).add(solverOptions);
		
		// parse variables
		po::store(po::parse_command_line(argc, argv, desc_cmdline), vm);
		std::ifstream inifile("settings.ini");
		po::store(po::parse_config_file(inifile, desc_file), vm);

		po::notify(vm);
	}
	
	bool has(const std::string& s) const {
		return vm.count(s);
	}

	bool verbose = false;
	bool quiet = false;
	bool mute = false;
	std::string validationtool;
	std::string outputDir;
	std::string wrongResultsDir;
	std::string statsXMLFile;
	std::vector<std::string> pathes;
	std::vector<std::string> smtratapps;
	std::vector<std::string> z3apps;
	std::vector<std::string> isatapps;
	std::vector<std::string> redlog_rlqeapps;
	std::vector<std::string> redlog_rlcadapps;
	std::vector<std::string> qepcadapps;
	std::vector<std::string> nodes;
	std::vector<std::string> composeFiles;
	
	friend std::ostream& operator<<(std::ostream& os, const Settings& s) {
		os << s.desc_cmdline << std::endl;
		return os;
	}
};

}