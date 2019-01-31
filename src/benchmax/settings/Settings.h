/**
 * @file Settings.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include "../utils/strings.h"

#include <carl/util/Singleton.h>

#include <any>
#include <chrono>
#include <ctime>
#include <fstream>
#include <map>
#include <memory>

namespace benchmax {
namespace settings {

template<typename T, typename V>
inline void finalize_settings(T&, const V&) {}

struct CoreSettings {
	bool show_help;
	bool show_settings;
	bool be_verbose;
	bool be_quiet;
};

struct OperationSettings {
	std::string backend;
	std::string convert_ods_filename;
	std::string convert_ods_filter;
};

struct BenchmarkSettings {
	bool use_wallclock;
	std::size_t limit_memory;
	std::chrono::seconds limit_time;
	std::vector<std::string> input_directories;
	std::string input_directories_common_prefix;
	std::string output_file_xml;
};
template<typename V>
inline void finalize_settings(BenchmarkSettings& s, const V& values) {
	s.limit_time = std::chrono::seconds(values["timeout"].template as<std::size_t>());
	s.input_directories_common_prefix = commonPrefix(s.input_directories);
}

struct ToolSettings {
	bool collect_statistics;
	std::vector<std::string> tools_generic;
	std::vector<std::string> tools_smtrat;
	std::vector<std::string> tools_smtrat_opb;
	std::vector<std::string> tools_minisatp;
	std::vector<std::string> tools_z3;
	std::string tools_common_prefix;
};
template<typename V>
inline void finalize_settings(ToolSettings& s, const V&) {
	s.tools_common_prefix = commonPrefix({
		s.tools_generic,
		s.tools_smtrat,
		s.tools_smtrat_opb,
		s.tools_minisatp,
		s.tools_z3
	});
}

struct Settings: public carl::Singleton<Settings> {
	friend carl::Singleton<Settings>;
private:
	std::map<std::string,std::any> mSettings = {
		{"core", CoreSettings()},
		{"operation", OperationSettings()},
		{"benchmarks", BenchmarkSettings()},
		{"tools", ToolSettings()},
	};

	Settings() = default;
public:

	template<typename T>
	T& get(const std::string& name) {
		auto it = mSettings.find(name);
		assert(it != mSettings.end());
		return std::any_cast<T&>(it->second);
	}
	template<typename T>
	T& add(const std::string& name) {
		auto res = mSettings.emplace(name, T{});
		assert(res.second);
		return std::any_cast<T&>(res.first->second);
	}
};

}


inline const settings::Settings& getSettings() {
	return settings::Settings::getInstance();
}

inline const auto& settings_core() {
	static const auto& s = settings::Settings::getInstance().get<settings::CoreSettings>("core");
	return s;
}
inline const auto& settings_operation() {
	static const auto& s = settings::Settings::getInstance().get<settings::OperationSettings>("operation");
	return s;
}
inline const auto& settings_benchmarks() {
	static const auto& s = settings::Settings::getInstance().get<settings::BenchmarkSettings>("benchmarks");
	return s;
}
inline const auto& settings_tools() {
	static const auto& s = settings::Settings::getInstance().get<settings::ToolSettings>("tools");
	return s;
}

}
