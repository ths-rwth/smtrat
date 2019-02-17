#pragma once

#include <carl/util/Singleton.h>
#include <carl/util/Settings.h>

#include <any>
#include <cassert>
#include <map>
#include <string>

namespace smtrat {
namespace settings {

struct CoreSettings {
	bool show_help;
	bool show_info;
	bool show_version;
	bool show_settings;
	bool show_cmake_options;
	bool show_strategy;
	bool show_license;
	std::string config_file;
};

struct SolverSettings {
	bool print_model;
	bool print_all_models;
	bool preprocess;
	std::string preprocess_output_file;
	bool preprocess_enable_cnf;
	bool analyze_file;
	bool print_timings;
};

struct ValidationSettings {
	bool log_lemmata;
	bool log_theory_calls;
	bool log_infeasible_subsets;
	std::string log_filename;
};

struct Settings: public carl::Singleton<Settings>, public carl::settings::Settings {
	friend carl::Singleton<Settings>;
private:
	Settings() {
		get<CoreSettings>("core");
		get<SolverSettings>("solver");
		get<ValidationSettings>("validation");
	}
};

}

inline const settings::Settings& Settings() {
	return settings::Settings::getInstance();
}

inline const auto& settings_core() {
	static const auto& s = settings::Settings::getInstance().get<settings::CoreSettings>("core");
	return s;
}
inline const auto& settings_solver() {
	static const auto& s = settings::Settings::getInstance().get<settings::SolverSettings>("solver");
	return s;
}
inline const auto& settings_validation() {
	static const auto& s = settings::Settings::getInstance().get<settings::ValidationSettings>("validation");
	return s;
}

}