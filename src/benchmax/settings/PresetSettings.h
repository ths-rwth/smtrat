#pragma once

#include <benchmax/settings/Settings.h>

namespace benchmax {
namespace settings {

struct PresetSettings {
	/// Use slurm on the RWTH HPC cluster.
	bool rwth_slurm;
	/// Name for this job.
	std::string rwth_slurm_name;
};

/// Registers preset settings with the settings parser.
void registerPresetSettings(SettingsParser* parser);

}

/// Return the Slurm settings.
inline const auto& settings_preset() {
	return settings_get<settings::PresetSettings>("presets");
}
}