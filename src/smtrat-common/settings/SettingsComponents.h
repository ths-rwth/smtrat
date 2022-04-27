#pragma once

#include "SettingsParser.h"

#include <carl-common/memory/Singleton.h>

#include <functional>
#include <vector>

namespace smtrat {

class SettingsComponents: public carl::Singleton<SettingsComponents> {
private:
	std::vector<std::function<void(SettingsParser&)>> mHooks;
public:
	void add(std::function<void(SettingsParser&)>&& f) {
		mHooks.emplace_back(f);
	}
	void add_to_parser(SettingsParser& parser) const {
		for (const auto& f: mHooks) {
			f(parser);
		}
	}
};

} // smtrat
