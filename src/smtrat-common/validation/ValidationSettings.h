#pragma once

// #include <smtrat-common/settings/Settings.h>
// #include <smtrat-common/settings/SettingsParser.h>
#include "../settings/Settings.h"
#include "../settings/SettingsParser.h"

namespace smtrat {
namespace validation {

struct ValidationSettings {
	bool export_as_smtlib;
	bool export_as_smtlib_flush;
	std::string smtlib_filename;

	std::vector<std::string> channels;
	bool channel_active(const std::string& key) const {
		for (const auto& c: channels) {
			if (key == c || key.rfind(c + ".", 0) == 0) {
				return true;
			}
		}
		return false;
	}
};

template<typename T>
void registerValidationSettings(T& parser) {
	namespace po = boost::program_options;
	auto& settings = settings::Settings::getInstance();
	auto& s = settings.get<ValidationSettings>("validation");

	parser.add("Validation settings").add_options()
		("validation.export-smtlib", po::bool_switch(&s.export_as_smtlib), "store validation formulas to smtlib file")
		("validation.export-smtlib-flush", po::bool_switch(&s.export_as_smtlib_flush), "store validation formulas to smtlib file after each time a lemma is produced (useful if the solver segfaults)")
		("validation.smtlib-filename", po::value<std::string>(&s.smtlib_filename)->default_value("validation.smt2"), "filename of smtlib output")
		("validation.channel", po::value<std::vector<std::string>>(&s.channels), "add a channel to be considered")
	;
}

}

inline const auto& settings_validation() {
	static const auto& s = settings::Settings::getInstance().get<validation::ValidationSettings>("validation");
	return s;
}

}
