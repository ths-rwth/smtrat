#include "SettingsParser.h"

#include "Settings.h"

namespace benchmax {

namespace po = boost::program_options;

SettingsParser::SettingsParser() {
	mPositional.add("input-file", 1);

	auto& settings = settings::Settings::getInstance();

	{
		auto& s = settings.get<settings::CoreSettings>("core");
		add("Core settings").add_options()
			("help", po::bool_switch(&s.show_help), "show help")
			("settings", po::bool_switch(&s.show_settings), "show settings that are used")
			("verbose", po::bool_switch(&s.be_verbose), "show more detailed output")
			("quiet", po::bool_switch(&s.be_quiet), "show only most important output")
			("config,c", po::value<std::string>(&s.config_file), "load config from the given config file")
		;
	}
	{
		auto& s = settings.get<settings::OperationSettings>("operation");
		add("Operational settings").add_options()
			("backend,b", po::value<std::string>(&s.backend), "Run benchmarks using the given backend. Possible values: \"condor\", \"local\", \"slurm\", \"ssh\".")
			("convert", po::value<std::string>(&s.convert_ods_filename), "Convert a XML result file to .ods")
			("convert-filter", po::value<std::string>(&s.convert_ods_filter)->default_value("Benchmax"), "XSLT filter name to import XML file into libreoffice")
		;
	}
}

}