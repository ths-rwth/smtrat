#pragma once

#include <benchmax/settings/Settings.h>

namespace benchmax {
namespace  settings {

/// Settings for SSH backend.
struct SSHBackendSettings {
	/// List of nodes to connect to.
	std::vector<std::string> nodes;
	/// Base directory for solvers.
	std::string basedir;
	/// Temporary directory for benchmarks and output files.
	std::string tmpdir;
	/// Use wallclock timeouts instead of CPU time.
	bool use_wallclock;
};

/// Registers SSH settings with settings parser.
void registerSSHBackendSettings(SettingsParser* parser);
}

/// Return the SSH settings.
inline const auto& settings_ssh() {
	return settings_get<settings::SSHBackendSettings>("backend-ssh");
}

}