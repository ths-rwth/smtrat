/**
 * @file ModuleSettings.h
 * @author Florian Corzilius
 *
 * @version 2015-09-09
 * Created on 2015-09-09.
 */

#pragma once
#include <iostream>

namespace smtrat {
struct ModuleSettings {
	static constexpr auto moduleName = "Module";

};

inline std::ostream& operator<<(std::ostream& os, const ModuleSettings& settings) {
	return os << settings.moduleName;
}
} // namespace smtrat
