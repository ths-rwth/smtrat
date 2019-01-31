#pragma once

#include "../settings/Settings.h"
#include "../settings/SettingsParser.h"

namespace benchmax {
struct SSHBackendSettings {
	std::vector<std::string> nodes;
	std::string basedir;
	std::string tmpdir;
};

template<typename T>
void registerSSHBackendSettings(T& parser) {
	auto& settings = settings::Settings::getInstance();
	auto& s = settings.add<SSHBackendSettings>("backend-ssh");
	
	parser.add("SSH Backend settings", s).add_options()
		("node,N", po::value<std::vector<std::string>>(&s.nodes), "remote computation nodes")
		("basedir", po::value<std::string>(&s.basedir)->default_value("~/"), "remote base directory")
		("tmpdir", po::value<std::string>(&s.tmpdir)->default_value("/tmp/"), "remote temporary directory")
	;
}

inline const auto& settings_ssh() {
	static const auto& s = settings::Settings::getInstance().get<SSHBackendSettings>("backend-ssh");
	return s;
}
}