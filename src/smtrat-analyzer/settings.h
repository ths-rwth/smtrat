#pragma once

#include <smtrat-common/settings/Settings.h>
#include <smtrat-common/settings/SettingsParser.h>
#include <smtrat-common/smtrat-common.h>

#include <string>

namespace smtrat {
namespace analyzer {

struct AnalysisSettings {
	bool enabled = false;
	bool analyze_cnf = false;
	std::string analyze_projections = "none";
};

template<typename T>
void registerAnalyzerSettings(T& parser) {
	namespace po = boost::program_options;
	auto& settings = settings::Settings::getInstance();
	auto& s = settings.get<AnalysisSettings>("analyzer");

	parser.add("Analysis settings").add_options()
			("analyze.enabled", po::bool_switch(&s.enabled), "enable formula analyzer")
			("analyze.projections", po::value<std::string>(&s.analyze_projections)->default_value("none"), "which CAD projections to analyze (all, collins, hong, mccallum, mccallum_partial, lazard, brown, none)")
			("analyze.cnf", po::bool_switch(&s.analyze_cnf)->default_value(false), "enable CNF analyzer")
	;
}

}

inline const auto& settings_analyzer() {
	static const auto& s = settings::Settings::getInstance().get<analyzer::AnalysisSettings>("analyzer");
	return s;
}

}