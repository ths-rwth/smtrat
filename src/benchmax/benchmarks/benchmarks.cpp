#include "benchmarks.h"

#include <benchmax/logging.h>
#include <benchmax/settings/Settings.h>

namespace benchmax {

std::vector<BenchmarkSet> loadBenchmarks() {
	std::vector<BenchmarkSet> benchmarks;
	for (const auto& p: settings_benchmarks().input_directories) {
		std::filesystem::path path(p);
		if (std::filesystem::exists(path)) {
			BENCHMAX_LOG_INFO("benchmax.benchmarks", "Adding benchmark " << path.native());
			benchmarks.emplace_back(path);
		} else {
			BENCHMAX_LOG_WARN("benchmax", "Benchmark path " << p << " does not exist.");
		}
	}
	return benchmarks;
}

}