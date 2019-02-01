#include "SettingsParser.h"

#include "Settings.h"

#include <boost/any.hpp>

namespace benchmax {
namespace settings {

std::ostream& operator<<(std::ostream& os, const boost::any& val) {
	if (val.empty()) {
		return os << "<empty>";
	} else if (boost::any_cast<bool>(&val)) {
		return os << std::boolalpha << boost::any_cast<bool>(val);
	} else if (boost::any_cast<std::string>(&val)) {
		return os << boost::any_cast<std::string>(val);
	}
	return os << "Unknown type";
}


std::ostream& operator<<(std::ostream& os, OptionPrinter op) {
	if (op.parser.argv_zero == nullptr) {
		os << "Usage: <binary> [options]";
	} else {
		os << "Usage: " << op.parser.argv_zero << " [options]";
	}
	for (unsigned i = 0; i < op.parser.mPositional.max_total_count(); ++i) {
		os << " " << op.parser.mPositional.name_for_position(i);
	}
	os << std::endl;
	return os << op.parser.mAllOptions;
}
std::ostream& operator<<(std::ostream& os, SettingsPrinter sp) {
	for (const auto& option: sp.parser.mAllOptions.options()) {
		auto value = sp.parser.mValues[option->canonical_display_name()];
		os << option->canonical_display_name() << " = " << value.value() << std::endl;
	}
	return os;
}

}

SettingsParser::SettingsParser() {
	mPositional.add("input-file", 1);

	auto& settings = settings::Settings::getInstance();

	{
		auto& s = settings.get<settings::CoreSettings>("core");
		add("Core settings", s).add_options()
			("help", po::bool_switch(&s.show_help), "show help")
			("settings", po::bool_switch(&s.show_settings), "show settings that are used")
			("verbose", po::bool_switch(&s.be_verbose), "show more detailed output")
			("quiet", po::bool_switch(&s.be_quiet), "show only most important output")
		;
	}
	{
		auto& s = settings.get<settings::OperationSettings>("operation");
		add("Operational settings", s).add_options()
			("backend,b", po::value<std::string>(&s.backend), "Run benchmarks using the given backend. Possible values: \"condor\", \"local\", \"slurm\", \"ssh\".")
			("convert", po::value<std::string>(&s.convert_ods_filename), "Convert a XML result file to .ods")
			("convert-filter", po::value<std::string>(&s.convert_ods_filter)->default_value("Benchmax"), "XSLT filter name to import XML file into libreoffice")
		;
	}
}

bool SettingsParser::parse_options(int argc, char* argv[]) {
	argv_zero = argv[0];
	po::store(
		po::command_line_parser(argc, argv).options(mAllOptions).positional(mPositional).run(),
		mValues
	);
	po::notify(mValues);
	for (const auto& f: mFinalizer) {
		f();
	}
	return true;
}

}