#pragma once

#include <benchmax/config.h>

#include <boost/program_options.hpp>
#include <benchmax/settings/Settings.h>

namespace benchmax {
namespace  settings {

struct SSHBackendSettings {
	std::vector<std::string> nodes;
	std::string basedir;
	std::string tmpdir;
};

template<typename T>
void registerSSHBackendSettings(T& parser) {
	namespace po = boost::program_options;
	auto& settings = settings::Settings::getInstance();
	auto& s = settings.add<SSHBackendSettings>("backend-ssh");
	
#ifdef BENCHMAX_SSH
	parser.add("SSH Backend settings", s).add_options()
#else
	parser.add("SSH Backend settings (disabled)", s).add_options()
#endif
		("ssh:node", po::value<std::vector<std::string>>(&s.nodes), "remote computation nodes")
		("ssh:basedir", po::value<std::string>(&s.basedir)->default_value("~/"), "remote base directory")
		("ssh:tmpdir", po::value<std::string>(&s.tmpdir)->default_value("/tmp/"), "remote temporary directory")
	;
}
}

inline const auto& settings_ssh() {
	static const auto& s = settings::Settings::getInstance().get<settings::SSHBackendSettings>("backend-ssh");
	return s;
}

}