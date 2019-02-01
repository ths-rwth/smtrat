#pragma once

#include <benchmax/settings/Settings.h>

namespace benchmax {
namespace  settings {

struct SSHBackendSettings {
	std::vector<std::string> nodes;
	std::string basedir;
	std::string tmpdir;
	bool use_wallclock;
};

void registerSSHBackendSettings(SettingsParser* parser);
}

inline const auto& settings_ssh() {
	return settings_get<settings::SSHBackendSettings>("backend-ssh");
}

}