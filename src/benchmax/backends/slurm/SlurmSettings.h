#pragma once

#include <benchmax/settings/Settings.h>

namespace benchmax {
namespace settings {

struct SlurmBackendSettings {
	std::size_t slices;
	std::string tmp_dir;
	bool keep_logs;
	std::string archive_log_file;
};

void registerSlurmBackendSettings(SettingsParser* parser);
}

inline const auto& settings_slurm() {
	return settings_get<settings::SlurmBackendSettings>("backend-slurm");
}

}