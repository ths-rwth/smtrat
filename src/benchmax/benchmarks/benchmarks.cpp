#include "benchmarks.h"

#include <benchmax/logging.h>
#include <benchmax/settings/SettingsParser.h>

namespace benchmax {

std::vector<BenchmarkSet> loadBenchmarks() {
	std::vector<BenchmarkSet> benchmarks;
	for (const auto& p : settings_benchmarks().input_directories) {
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

namespace settings {
void registerBenchmarkSettings(SettingsParser* parser) {
	namespace po = boost::program_options;
	auto& settings = settings::Settings::getInstance();
	auto& s = settings.add<settings::BenchmarkSettings>("benchmarks");
	
	parser->add("Benchmark settings", s).add_options()
		("wallclock", po::bool_switch(&s.use_wallclock), "Use wall clock for timeout")
		("memory,M", po::value<std::size_t>(&s.limit_memory)->default_value(1024), "memory limit for all competing solvers in megabytes")
		("timeout,T", po::value<std::size_t>()->default_value(60), "timeout for all tools in seconds")
		("directory,D", po::value<std::vector<std::string>>(&s.input_directories), "path to look for benchmarks (several are possible)")
		("output-dir", po::value<std::string>(&s.output_dir), "Output directory.")
		("output-xml,X", po::value<std::string>(&s.output_file_xml)->default_value("stats.xml"), "filename for xml output file")
	;
}
}

}