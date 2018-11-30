#pragma once

#include <carl/util/Singleton.h>
#include <string>

namespace smtrat {
namespace settings {

struct CoreSettings {
	bool show_help;
	bool show_info;
	bool show_version;
	bool show_settings;
	bool show_cmake_options;
	bool show_license;
};

struct ParserSettings {
	bool read_dimacs;
	bool read_opb;
	std::string input_file;
};

struct SolverSettings {
	bool print_model;
	bool print_all_models;
	bool preprocess;
	std::string preprocess_output_file;
	bool print_statistics;
	bool print_strategy;
	bool print_timings;
};

struct ValidationSettings {
	bool log_lemmata;
	bool log_theory_calls;
	bool log_infeasible_subsets;
	std::string log_filename;
};

struct Settings: public carl::Singleton<Settings> {
	CoreSettings core;
	ParserSettings parser;
	SolverSettings solver;
	ValidationSettings validation;
};

}

inline const auto& Settings() {
	return settings::Settings::getInstance();
}

}