#pragma once

#include "Tool.h"

#include <benchmax/settings/Settings.h>

#include <memory>
#include <vector>

namespace benchmax {

using ToolPtr = std::unique_ptr<Tool>;
using Tools = std::vector<ToolPtr>;

template<typename T>
void createTools(const std::vector<std::string>& arguments, Tools& tools);

Tools loadTools();

namespace settings {

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
		s.tools_generic, s.tools_smtrat, s.tools_smtrat_opb,
		s.tools_minisatp, s.tools_z3
	});
}
void registerToolSettings(SettingsParser* parser);
} // namespace settings

inline const auto& settings_tools() {
	return settings_get<settings::ToolSettings>("tools");
}

} // namespace benchmax
