#include "PresetSettings.h"

#include <benchmax/logging.h>
#include <benchmax/settings/SettingsParser.h>

#include <benchmax/backends/slurm/SlurmSettings.h>
#include <benchmax/benchmarks/benchmarks.h>
#include <benchmax/settings/Settings.h>

#include <cstdlib>

namespace benchmax {

namespace settings {

/// Postprocess preset settings.
bool finalize_preset_settings(PresetSettings& s, boost::program_options::variables_map& values) {
	if (s.rwth_slurm) {
		auto work_cstr = std::getenv("WORK");
		if (work_cstr == nullptr) {
			BENCHMAX_LOG_WARN("benchmax.preset", "The preset rwth-slurm is selected but $WORK is not set. We use $WORK = \"work\" for now.");
		}
		std::string work(work_cstr != nullptr ? work_cstr : "WORK");
		carl::settings::default_to(values, "backend", std::string("slurm"));
		carl::settings::default_to(values, "output-xml", std::string("stats_" + s.rwth_slurm_name + ".xml"));
		carl::settings::default_to(values, "slurm.keep-logs", true);
		carl::settings::default_to(values, "slurm.archive-logs", std::string("logs-" + s.rwth_slurm_name));
		carl::settings::default_to(values, "slurm.tmp-dir", std::string(work + "/" + s.rwth_slurm_name));
		carl::settings::default_to(values, "slurm.sbatch-options", std::string("-C hpcwork"));
		return true;
	}
	return false;
}

void registerPresetSettings(SettingsParser* parser) {
	namespace po = boost::program_options;
	auto& settings = settings::Settings::getInstance();
	auto& s = settings.get<settings::PresetSettings>("presets");
	
	parser->add_finalizer([&s](auto& values){
		return finalize_preset_settings(s, values);
	});
	parser->add("Presets").add_options()
		("preset.rwth-slurm", po::bool_switch(&s.rwth_slurm), "Use SLURM on the RWTH HPC cluster")
		("preset.rwth-slurm-name", po::value<std::string>(&s.rwth_slurm_name), "Short name for file naming")
	;
}
}

}