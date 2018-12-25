/**
 * @file SettingsManager.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <iostream>
#include <map>
#include <smtrat-common/smtrat-common.h>
#ifdef __VS
#pragma warning(push, 0)
#include <boost/spirit/home/support/detail/hold_any.hpp>
#pragma warning(pop)
#else
#include <boost/spirit/home/support/detail/hold_any.hpp>
#endif


#include <carl/util/Singleton.h>

namespace smtrat {

class SettingsManager: public carl::Singleton<SettingsManager> {
public:
	typedef boost::spirit::hold_any any;
	typedef std::map<std::string, any> ModuleOptions;
	typedef std::map<std::string, ModuleOptions> OptionMap;
	
	class SettingsPrinter {
	private:
		OptionMap options;
		friend std::ostream& operator<<(std::ostream& os, const SettingsPrinter& settings);
	public:
		SettingsPrinter(const OptionMap& options): options(options) {}
	};
	
private:
	OptionMap options;
	OptionMap allOptions;
	
	static bool  handle(const std::string&) {
		return true;
	}
	
	template<typename Value, typename... Args>
	static bool handle(const std::string& module, const std::string& option, const Value& _default, const Value& value, Args&&... args) {
		if (_default != value) {
			SettingsManager::getInstance().options[module][option] = value;
		}
		SettingsManager::getInstance().allOptions[module][option] = value;
		return handle(module, std::forward<Args>(args)...);
	}
public:
	
	template<typename... Args>
	static bool addModule(const std::string& module, Args&&... args) {
		return handle(module, std::forward<Args>(args)...);
	}
	
	SettingsPrinter changed() const {
		return SettingsPrinter(options);
	}
	SettingsPrinter all() const {
		return SettingsPrinter(allOptions);
	}
};

inline std::ostream& operator<<(std::ostream& os, const SettingsManager::SettingsPrinter& settings) {
	for (const auto& module: settings.options) {
		for (const auto& option: module.second) {
			os << module.first << "::" << option.first << " = " << option.second << std::endl;
		}
	}
	return os;
}

}