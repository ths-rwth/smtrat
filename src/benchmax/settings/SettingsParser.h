#pragma once

#include <carl/util/Singleton.h>
#include <carl/util/SettingsParser.h>

#include "Settings.h"

namespace benchmax {

/**
 * Generic class to manage settings parsing using boost::program_options.
 * Allows to register dynamically add new options_description object and manages parsing them from command line and config file.
 * When everything is registed finalize() has to be called to construct the full option description.
 */
class SettingsParser: public carl::settings::SettingsParser, public carl::Singleton<SettingsParser> {
	friend carl::Singleton<SettingsParser>;

	SettingsParser();
};

} // smtrat
