#include "SlurmSettings.h"

#include <benchmax/settings/SettingsParser.h>

namespace benchmax {
namespace settings {

void registerSlurmBackendSettings(SettingsParser* parser) {
	namespace po = boost::program_options;
	auto& settings = settings::Settings::getInstance();
	auto& s = settings.add<SlurmBackendSettings>("backend-slurm");
	
	parser->add("Slurm Backend settings").add_options()
		("slurm.slices", po::value<std::size_t>(&s.slices)->default_value(1000), "number of slices for array job")
		("slurm.tmp-dir", po::value<std::string>(&s.tmp_dir)->default_value("/tmp/"), "temporary directory")
		("slurm.keep-logs", po::bool_switch(&s.keep_logs), "do not delete log files")
		("slurm.archive-logs", po::value<std::string>(&s.archive_log_file)->value_name("filename"), "store log files in this tgz archive")
	;
}
}
}