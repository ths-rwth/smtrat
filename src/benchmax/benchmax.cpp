/**
 * @file benchmax.cpp
 *
 * @author Sebastian Junges
 * @author Ulrich Loup
 *
 * @since 2012-02-01
 * @version 2013-04-23
 */

#include <csignal>
#include <filesystem>
#include <iostream>

#include "config.h"
#include "logging.h"
#include "backends/Backends.h"
#include "benchmarks/benchmarks.h"
#include "tools/Tools.h"
#include "settings/Settings.h"
#include "settings/SettingsParser.h"
#include "Stats.h"


using namespace benchmax;

/**
 * Initialized the application.
 * 
 * Takes care of loading settings from the command line and a config file.
 * Afterwards checks for all options that are handled easily like being verbose or showing the help.
 * Might signal to stop execution by returning true.
 * @param argc argc as passed to main()
 * @param argv argv as passed to main()
 * @return true if the application should stop.
 */
bool init_application(int argc, char** argv) {

	logging_configure();

	auto& parser = SettingsParser::getInstance();
	benchmax::settings::registerBenchmarkSettings(&parser);
	benchmax::settings::registerToolSettings(&parser);
	benchmax::settings::registerSlurmBackendSettings(&parser);
	benchmax::settings::registerSSHBackendSettings(&parser);
	parser.finalize();
	parser.parse_options(argc, argv);

	if (settings_core().be_quiet) {
		logging_quiet();
	}
	if (settings_core().be_verbose) {
		logging_verbose();
	}
	if (settings_core().show_help) {
		std::cout << parser.print_help() << std::endl;
		return false;
	}
	if (settings_core().show_settings) {
		std::cout << parser.print_options() << std::endl;
		return false;
	}

	if (settings_operation().convert_ods_filename != "") {
		std::string filename = settings_operation().convert_ods_filename;
		std::string filter = settings_operation().convert_ods_filter;
		BENCHMAX_LOG_INFO("benchmax.convert", "Converting " << filename << " to ods using import filer " << filter);
		std::stringstream ss;
		ss << "libreoffice --headless --infilter=" << filter << " --convert-to ods " << filename;
		system(ss.str().c_str());
		return false;
	}
	
	
	//if(s.has("compose")) {
	//	Stats::composeStats(s.composeFiles);
	//	return false;
	//}
	//else if(Settings::ProduceLatex)
	//{
	//	Stats::createStatsCompose(settings_benchmarks().output_dir + "latexCompose.xsl");
	//	system(
	//	std::string("xsltproc -o " + settings_benchmarks().output_dir + "results.tex " + Settings::outputDir + "latexCompose.xsl "
	//				+ settings_benchmarks().output_file_xml).c_str());
	//	fs::remove(fs::path(settings_benchmarks().output_dir + "latexCompose.xsl"));
	//}

	if (settings_benchmarks().output_dir != "") {
		std::filesystem::path oloc = std::filesystem::path(settings_benchmarks().output_dir);
		if(!std::filesystem::exists(oloc) ||!std::filesystem::is_directory(oloc))
		{
			BENCHMAX_LOG_FATAL("benchmax", "Output directory does not exist: " << oloc);
			exit(0);
		}
	}

	return true;
}

/**
 * Handles the interrupt signal.
 */
void handleSignal(int)
{
	BENCHMAX_LOG_WARN("benchmax", "User abort!");
	exit(-1);
}

/**
 * Main program.
 */
int main(int argc, char** argv)
{
	std::signal(SIGINT, &handleSignal);
	
	if (!init_application(argc, argv)) {
		return 0;
	}
	
	Tools tools = loadTools();
	if (tools.empty()) {
		BENCHMAX_LOG_ERROR("benchmax", "No usable tools were found.");
		return 0;
	}

	BenchmarkSet benchmarks = loadBenchmarks();
	if(benchmarks.size() == 0) {
		BENCHMAX_LOG_ERROR("benchmax", "No benchmarks were found. Specify a valid location with --directory.");
		return 0;
	}
	benchmax::run_backend(settings_operation().backend, tools, benchmarks);

	return 0;
}
