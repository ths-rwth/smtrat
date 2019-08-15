#pragma once

#include <smtrat-common/smtrat-common.h>

#include <string>

namespace smtrat {
namespace analyzer {

struct AnalysisSettings {
	bool analyze_file = false;
	bool analyze_projections = false;
};

template<typename T>
void registerAnalyzerSettings(T& parser) {
#ifdef CLI_ENABLE_FORMULAPARSER
	namespace po = boost::program_options;
	auto& settings = settings::Settings::getInstance();
	auto& s = settings.get<AnalysisSettings>("analyzer");

	parser.add("Analysis settings").add_options()
			("analyze.file", po::bool_switch(&s.analyze_file), "parse file and analyze it")
			("analyze.projections", po::bool_switch(&s.analyze_projections), "analyze different CAD projections")
	;
#endif
}

}

inline const auto& settings_analyzer() {
	static const auto& s = settings::Settings::getInstance().get<analyzer::AnalysisSettings>("analyzer");
	return s;
}

}