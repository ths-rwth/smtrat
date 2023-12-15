#pragma once

#include "BenchmarkSet.h"

#include <benchmax/settings/Settings.h>

#include <vector>

namespace benchmax {

/// Loads benchmark files from directory specified in settings.
BenchmarkSet loadBenchmarks();

namespace settings {

/// Settings for benchmarks.
struct BenchmarkSettings {
	/// Memory limit in megabytes.
	carl::settings::binary_quantity limit_memory;
	/// Time limit in seconds.
	carl::settings::duration limit_time;
	/// Grace time in seconds.
	carl::settings::duration grace_time;
	/// Lift of input directories.
	std::vector<std::filesystem::path> input_directories;
	/// Common prefix of input directories (to shorten filenames in output).
	std::filesystem::path input_directories_common_prefix;
	/// Output directory.
	std::filesystem::path output_dir;
	/// Filename of xml file.
	std::filesystem::path output_file_xml;
	/// Filename of xml file.
	std::filesystem::path output_file_csv;
};

/// Registers benchmark settings with the settings parser.
void registerBenchmarkSettings(SettingsParser* parser);
} // namespace settings

/// Return the benchmark settings.
inline const auto& settings_benchmarks() {
	return settings_get<settings::BenchmarkSettings>("benchmarks");
}

} // namespace benchmax