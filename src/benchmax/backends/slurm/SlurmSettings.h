#pragma once

#include <benchmax/settings/Settings.h>

namespace benchmax {
namespace settings {

/// Settings for the Slurm backend.
struct SlurmBackendSettings {
	/// Number of array jobs within one job.
	std::size_t array_size;
	/// Size of one slice that is handled in one array job.
	std::size_t slice_size;
	/// Temporary directory for output files.
	std::string tmp_dir;
	/// Do not remove logs from file system if set to true.
	bool keep_logs;
	/// Puts logs to some archive.
	std::string archive_log_file;
	/// Additional options passed on to slurm.
	std::string sbatch_options;
};

/// Registers Slurm settings with the settings parser.
void registerSlurmBackendSettings(SettingsParser* parser);
}

/// Return the Slurm settings.
inline const auto& settings_slurm() {
	return settings_get<settings::SlurmBackendSettings>("backend-slurm");
}

}