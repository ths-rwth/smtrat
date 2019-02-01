/**
 * @file Settings.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include "../utils/strings.h"

#include <carl/util/Singleton.h>

#include <any>
#include <cassert>
#include <chrono>
#include <ctime>
#include <fstream>
#include <map>
#include <memory>

namespace benchmax {

class SettingsParser;

namespace settings {

template<typename T, typename V>
inline void finalize_settings(T&, const V&) {}

struct CoreSettings {
	bool show_help;
	bool show_settings;
	bool be_verbose;
	bool be_quiet;

	long start_time = std::time(nullptr);
};

struct OperationSettings {
	std::string backend;
	std::string convert_ods_filename;
	std::string convert_ods_filter;
};

struct Settings: public carl::Singleton<Settings> {
	friend carl::Singleton<Settings>;
private:
	std::map<std::string,std::any> mSettings = {
		{"core", CoreSettings()},
		{"operation", OperationSettings()}
	};

	Settings() = default;
public:

	template<typename T>
	T& get(const std::string& name) {
		auto it = mSettings.find(name);
		assert(it != mSettings.end());
		return std::any_cast<T&>(it->second);
	}
	template<typename T>
	T& add(const std::string& name) {
		auto res = mSettings.emplace(name, T{});
		assert(res.second);
		return std::any_cast<T&>(res.first->second);
	}
};

}


inline const settings::Settings& getSettings() {
	return settings::Settings::getInstance();
}
template<typename T>
inline const auto& settings_get(const std::string& name) {
	static const auto& s = settings::Settings::getInstance().get<T>(name);
	return s;
}

inline const auto& settings_core() {
	return settings_get<settings::CoreSettings>("core");
}
inline const auto& settings_operation() {
	return settings_get<settings::OperationSettings>("operation");
}

}
