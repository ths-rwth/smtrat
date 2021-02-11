#pragma once

#include <benchmax/settings/Settings.h>

namespace benchmax {
namespace  settings {

/// Settings for local backend.
struct LocalBackendSettings {
	/// Measure the peak memory usage of each call.
	//bool measure_peak_memory;
};

/// Registers local settings with settings parser.
void registerLocalBackendSettings(SettingsParser* parser);
}

/// Return the local settings.
inline const auto& settings_local() {
	return settings_get<settings::LocalBackendSettings>("backend-local");
}

}