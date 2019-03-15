#pragma once

#include <carl/util/Singleton.h>
#include <carl-settings/SettingsParser.h>

namespace smtrat {

class SettingsParser: public carl::settings::SettingsParser, public carl::Singleton<SettingsParser> {
	friend carl::Singleton<SettingsParser>;

	SettingsParser();
};

} // smtrat
