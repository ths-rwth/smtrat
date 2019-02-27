/**
 * @file Settings.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <benchmax/utils/filesystem.h>
#include <carl/util/Singleton.h>
#include <carl/util/Settings.h>

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
struct Settings: public carl::Singleton<Settings>, public carl::settings::Settings {
	friend carl::Singleton<Settings>;
private:
	Settings() {
		get<CoreSettings>("core");
		get<OperationSettings>("operation");
	};
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
