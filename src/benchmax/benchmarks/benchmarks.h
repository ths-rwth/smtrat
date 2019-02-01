#pragma once

#include "BenchmarkSet.h"

#include <benchmax/settings/Settings.h>

#include <vector>

namespace benchmax {

std::vector<BenchmarkSet> loadBenchmarks();

namespace settings {

struct BenchmarkSettings {
	bool use_wallclock;
	std::size_t limit_memory;
	std::chrono::seconds limit_time;
	std::vector<std::string> input_directories;
	std::string input_directories_common_prefix;
	std::string output_dir;
	std::string output_file_xml;
};
template<typename V>
inline void finalize_settings(BenchmarkSettings& s, const V& values) {
	s.limit_time = std::chrono::seconds(values["timeout"].template as<std::size_t>());
	s.input_directories_common_prefix = commonPrefix(s.input_directories);
}

void registerBenchmarkSettings(SettingsParser* parser);
} // namespace settings

inline const auto& settings_benchmarks() {
	return settings_get<settings::BenchmarkSettings>("benchmarks");
}

} // namespace benchmax