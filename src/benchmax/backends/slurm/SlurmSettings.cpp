#include "SlurmSettings.h"

#include <benchmax/settings/SettingsParser.h>

namespace benchmax {
namespace settings {

void registerSlurmBackendSettings(SettingsParser* parser) {
	namespace po = boost::program_options;
	auto& settings = settings::Settings::getInstance();
	auto& s = settings.add<SlurmBackendSettings>("backend-slurm");
	
	parser->add("Slurm Backend settings").add_options()
		("slurm.array-size", po::value<std::size_t>(&s.array_size)->default_value(1000), "number of array jobs per job")
		("slurm.slice-size", po::value<std::size_t>(&s.slice_size)->default_value(10), "number of individual tasks per array job")
		("slurm.tmp-dir", po::value<std::string>(&s.tmp_dir)->default_value("/tmp/"), "temporary directory")
		("slurm.keep-logs", po::bool_switch(&s.keep_logs), "do not delete log files")
		("slurm.archive-logs", po::value<std::string>(&s.archive_log_file)->value_name("filename"), "store log files in this tgz archive")
	;
}
}
}