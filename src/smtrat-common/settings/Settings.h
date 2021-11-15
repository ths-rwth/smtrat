#pragma once

#include <carl/util/Singleton.h>
#include <carl-settings/Settings.h>

#include <any>
#include <cassert>
#include <map>
#include <string>
#include <sstream>
#include <functional>

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
	bool convert_to_cnf_dimacs;
	bool convert_to_cnf_smtlib;
};

struct ModuleSettings {
	std::vector<std::string> parameters;

private:
	std::function<bool(const std::string&)> has_option;
	std::function<const std::string&(const std::string&)> get_option;

public:
	ModuleSettings() : has_option([](const std::string&){return false;}), get_option([](const std::string&){return "";}) {
	}

	void set_callbacks(std::function<bool(const std::string&)> callback_has, std::function<const std::string&(const std::string&)> callback_get) {
		has_option = callback_has;
		get_option = callback_get;
	}

	template<typename T>
	T get(const std::string& key, T default_value) const {
		if (has_option(key)) {
			std::istringstream iss(get_option(key));
			T value;
			iss >> value;
			return value;	
		} else {
			for (const auto& param : parameters) {
				std::string p_key = param.substr(0, param.find("="));
				if (p_key == key) {
					std::istringstream iss(param.substr(param.find("=")+1));
					T value;
					iss >> value;
					return value;		
				}
			}
		}
        return default_value;
	}
};

struct Settings: public carl::Singleton<Settings>, public carl::settings::Settings {
	friend carl::Singleton<Settings>;
private:
	Settings() {
		get<CoreSettings>("core");
		get<SolverSettings>("solver");
		get<ModuleSettings>("module");
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
inline const auto& settings_module() {
	static const auto& s = settings::Settings::getInstance().get<settings::ModuleSettings>("module");
	return s;
}

}