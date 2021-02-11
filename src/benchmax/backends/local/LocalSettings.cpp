#include "LocalSettings.h"

#include <benchmax/config.h>
#include <benchmax/settings/SettingsParser.h>

namespace benchmax {
namespace settings {

void registerLocalBackendSettings(SettingsParser* parser) {
	namespace po = boost::program_options;
	auto& settings = settings::Settings::getInstance();
	auto& s = settings.get<LocalBackendSettings>("backend-local");
	
	parser->add("Local Backend settings").add_options()
		//("local.measurepeakmemory", po::bool_switch(&s.measure_peak_memory), "measure the peak memory usage of each call")
	;
}
}
}