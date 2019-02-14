#pragma once

#include <smtrat-common/settings/Settings.h>
#include <smtrat-common/settings/SettingsParser.h>

namespace smtrat {
namespace statistics {

struct StatisticsSettings {
	bool export_as_xml;
	std::string xml_filename;
	bool print_as_smtlib;
};

template<typename T>
void registerStatisticsSettings(T& parser) {
	namespace po = boost::program_options;
	auto& settings = settings::Settings::getInstance();
	auto& s = settings.get<StatisticsSettings>("statistics");
	
	parser.add("Statistics settings").add_options()
		("stats.export-xml", po::bool_switch(&s.export_as_xml), "store statistics to xml file")
		("stats.xml-filename", po::value<std::string>(&s.xml_filename)->default_value("stats.xml"), "filename of xml output")
		("stats.print", po::bool_switch(&s.print_as_smtlib), "print statistics to stdout")
	;
}

}

inline const auto& settings_statistics() {
	static const auto& s = settings::Settings::getInstance().get<statistics::StatisticsSettings>("statistics");
	return s;
}

}
