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

// Predeclaration.
class SettingsParser;

namespace settings {

/**
 * Hook to be called when settings have been parsed.
 * This allows to compute some advanced settings like a common prefix of paths.
 * This is the generic (no-op) version that individual settings may specialize.
 */
template<typename T, typename V>
inline void finalize_settings(T&, const V&) {}

/// Core settings.
struct CoreSettings {
	/// Whether to show the command-line help.
	bool show_help;
	/// Whether to show the configured settings.
	bool show_settings;
	/// Whether to be more verbose.
	bool be_verbose;
	/// Whether to be more quiet.
	bool be_quiet;
	/// Path of an optional config file.
	std::string config_file;

	/// Timestamp the binary was started.
	long start_time = std::time(nullptr);
};

/// Operation settings.
struct OperationSettings {
	/// Name of the backend to be used.
	std::string backend;
	/// Name of the xml file to convert to an ods file.
	std::string convert_ods_filename;
	/// Name of the xslt filter used for ods import.
	std::string convert_ods_filter;
};

/**
 * Generic class to manage runtime settings.
 * Essentially stores all (named) settings in a map<string,any> and retrieves settings classes when requested.
 */
struct Settings: public carl::Singleton<Settings> {
	friend carl::Singleton<Settings>;
private:
	/// Stores the actual settings.
	std::map<std::string,std::any> mSettings = {
		{"core", CoreSettings()},
		{"operation", OperationSettings()}
	};

	Settings() = default;
public:
	/**
	 * Retrieves a settings object by name.
	 * Asserts that
	 * - a settings object with the given name exists and
	 * - the stored settings object has the type T.
	 * @param name Name of the settings object.
	 * return Settings object.
	 */
	template<typename T>
	T& get(const std::string& name) {
		auto it = mSettings.find(name);
		assert(it != mSettings.end());
		return std::any_cast<T&>(it->second);
	}
	/**
	 * Stores a new settings object by name with type T.
	 * Asserts that no settings object with the given name exists yet.
	 * @param name Name of the settings object.
	 * return Settings object.
	 */
	template<typename T>
	T& add(const std::string& name) {
		auto res = mSettings.emplace(name, T{});
		assert(res.second);
		return std::any_cast<T&>(res.first->second);
	}
};

}

/// Helper function to obtain settings by name and type.
template<typename T>
inline const auto& settings_get(const std::string& name) {
	static const auto& s = settings::Settings::getInstance().get<T>(name);
	return s;
}

/// Retrieved core settings.
inline const auto& settings_core() {
	return settings_get<settings::CoreSettings>("core");
}
/// Retrieved operation settings.
inline const auto& settings_operation() {
	return settings_get<settings::OperationSettings>("operation");
}

}
