#pragma once

#include <carl/util/Singleton.h>
#include <carl/util/SettingsParser.h>

namespace smtrat {

class SettingsParser: public carl::settings::SettingsParser, public carl::Singleton<SettingsParser> {
	friend carl::Singleton<SettingsParser>;

	SettingsParser();
};

} // smtrat
