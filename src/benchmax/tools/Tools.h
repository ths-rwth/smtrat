#pragma once

#include "Tool.h"

#include <benchmax/logging.h>
#include <benchmax/settings/Settings.h>

#include <filesystem>
#include <memory>
#include <vector>

namespace benchmax {

/// A std::unique_ptr to a Tool.
using ToolPtr = std::unique_ptr<Tool>;
/// A vector of ToolPtr.
using Tools = std::vector<ToolPtr>;

/**
 * Create tools of a given type T from a list of binaries and store them in tools.
 */
template<typename T>
void createTools(const std::vector<std::filesystem::path>& arguments, Tools& tools);

/// Load all tools from the tool settings.
Tools loadTools();

namespace settings {

/// Tool-related settings.
struct ToolSettings {
	/// Whether or not to collect statistics.
	bool collect_statistics;
	/// Generic tools.
	std::vector<std::filesystem::path> tools_generic;
	/// MathSAT with SMT-LIB interface.
	std::vector<std::filesystem::path> tools_mathsat;
	/// Minisat with DIMACS interface.
	std::vector<std::filesystem::path> tools_minisat;
	/// Minisatp with OPB interface.
	std::vector<std::filesystem::path> tools_minisatp;
	/// SMT-RAT with SMT-LIB interface.
	std::vector<std::filesystem::path> tools_smtrat;
	/// SMT-RAT with OPB interface.
	std::vector<std::filesystem::path> tools_smtrat_opb;
	/// SMT-RAT formula analyzer.
	std::vector<std::filesystem::path> tools_smtrat_analyzer;
	/// z3 with SMT-LIB interface.
	std::vector<std::filesystem::path> tools_z3;
	/// Common prefix of tool binaries to simplify output.
	std::filesystem::path tools_common_prefix;
};

/// Registers tool settings with the settings parser.
void registerToolSettings(SettingsParser* parser);
} // namespace settings

/// Returns the tool settings.
inline const auto& settings_tools() {
	return settings_get<settings::ToolSettings>("tools");
}

} // namespace benchmax
