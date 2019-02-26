#include "benchmarks.h"

#include <benchmax/logging.h>
#include <benchmax/settings/SettingsParser.h>

namespace benchmax {

BenchmarkSet loadBenchmarks() {
	BenchmarkSet benchmarks;
	for (const auto& p : settings_benchmarks().input_directories) {
		std::filesystem::path path(p);
		if (std::filesystem::exists(path)) {
			BENCHMAX_LOG_INFO("benchmax.benchmarks", "Adding benchmark " << path.native());
			benchmarks.add_directory(path);
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
	
	parser->add_finalizer([&s](const auto& values){
		finalize_benchmark_settings(s, values);
	});
	parser->add("Benchmark settings").add_options()
		("memory,M", po::value<std::size_t>(&s.limit_memory)->default_value(1024), "memory limit in megabytes")
		("timeout,T", po::value<carl::settings::duration>(&s.limit_time)->default_value(std::chrono::seconds(60))->value_name("time"), "timeout in seconds")
		("directory,D", po::value<std::vector<std::filesystem::path>>(&s.input_directories), "path to look for benchmarks")
		("output-dir", po::value<std::filesystem::path>(&s.output_dir), "output directory")
		("output-xml,X", po::value<std::filesystem::path>(&s.output_file_xml)->default_value("stats.xml"), "filename for xml output file")
	;
}
}

}