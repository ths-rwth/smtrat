#pragma once

#include <smtrat-common/smtrat-common.h>

#include <string>

namespace smtrat {
namespace analyzer {

struct AnalysisSettings {
	bool analyze_file = false;
	std::string analyze_projections = "none";
};

template<typename T>
void registerAnalyzerSettings(T& parser) {
#ifdef CLI_ENABLE_FORMULAPARSER
	namespace po = boost::program_options;
	auto& settings = settings::Settings::getInstance();
	auto& s = settings.get<AnalysisSettings>("analyzer");

	parser.add("Analysis settings").add_options()
			("analyze.file", po::bool_switch(&s.analyze_file), "parse file and analyze it")
			("analyze.projections", po::value<std::string>(&s.analyze_projections)->default_value("none"), "which CAD projections to analyze (all, collins, hong, mccallum, mccallum_partial, lazard, brown, none)")
	;
#endif
}

}

inline const auto& settings_analyzer() {
	static const auto& s = settings::Settings::getInstance().get<analyzer::AnalysisSettings>("analyzer");
	return s;
}

}