#include "SSHSettings.h"

#include <benchmax/config.h>
#include <benchmax/settings/SettingsParser.h>

namespace benchmax {
namespace settings {

void registerSSHBackendSettings(SettingsParser* parser) {
	namespace po = boost::program_options;
	auto& settings = settings::Settings::getInstance();
	auto& s = settings.get<SSHBackendSettings>("backend-ssh");
	
#ifdef BENCHMAX_SSH
	parser->add("SSH Backend settings").add_options()
#else
	parser->add("SSH Backend settings (disabled)").add_options()
#endif
		("ssh.node", po::value<std::vector<std::string>>(&s.nodes), "remote computation nodes")
		("ssh.basedir", po::value<std::string>(&s.basedir)->default_value("~/"), "remote base directory")
		("ssh.tmpdir", po::value<std::string>(&s.tmpdir)->default_value("/tmp/"), "remote temporary directory")
		("ssh.wallclock", po::bool_switch(&s.use_wallclock), "use wall clock for timeout")
		("ssh.resolvedeps", po::bool_switch(&s.resolve_deps), "resolve and upload dependencies of binary")
	;
}
}
}