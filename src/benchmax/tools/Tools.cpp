#include "Tools.h"

#include "MathSAT.h"
#include "Minisatp.h"
#include "SMTRAT.h"
#include "SMTRAT_OPB.h"
#include "Z3.h"

#include <benchmax/settings/SettingsParser.h>
#include <benchmax/logging.h>
#include <regex>

namespace benchmax {

template<typename T>
void createTools(const std::vector<std::filesystem::path>& arguments, Tools& tools) {
	std::regex r("([^ ]+) *(.*)");
	for (const auto& arg: arguments) {
		std::smatch matches;
		if (std::regex_match(arg.native(), matches, r)) {
			fs::path path = std::filesystem::canonical(fs::path(matches[1]));
			if (!fs::is_regular_file(path)) {
				BENCHMAX_LOG_WARN("benchmax", "The tool " << path << " does not seem to be a file. We skip it.");
				continue;
			}
			const fs::perms executable = fs::perms::others_exec | fs::perms::group_exec | fs::perms::owner_exec;
			if ((fs::status(path).permissions() & executable) == fs::perms::none) {
				BENCHMAX_LOG_WARN("benchmax", "The tool " << path << " does not seem to be executable. We skip it.");
				continue;
			}
			BENCHMAX_LOG_DEBUG("benchmax.tools", "Adding tool " << path << " with arguments \"" << matches[2] << "\".");
			tools.emplace_back(std::make_unique<T>(path, matches[2]));
		}
	}
}

Tools loadTools() {
	Tools tools;
	createTools<Tool>(settings_tools().tools_generic, tools);
	createTools<MathSAT>(settings_tools().tools_mathsat, tools);
	createTools<Minisatp>(settings_tools().tools_minisatp, tools);
	createTools<SMTRAT>(settings_tools().tools_smtrat, tools);
	createTools<SMTRAT_OPB>(settings_tools().tools_smtrat_opb, tools);
	createTools<Z3>(settings_tools().tools_z3, tools);
	return tools;
}

namespace settings {

/// Postprocess settings to compute common prefix.
bool finalize_tool_settings(ToolSettings& s, const boost::program_options::variables_map&) {
	s.tools_common_prefix = common_prefix({
		s.tools_generic, s.tools_smtrat, s.tools_smtrat_opb,
		s.tools_minisatp, s.tools_z3
	});
	BENCHMAX_LOG_DEBUG("benchmax.tools", "Common tool prefix is " << s.tools_common_prefix);
	return false;
}

void registerToolSettings(SettingsParser* parser) {
	namespace po = boost::program_options;
	auto& settings = settings::Settings::getInstance();
	auto& s = settings.get<settings::ToolSettings>("tools");

	parser->add_finalizer([&s](const auto& values){
		return finalize_tool_settings(s, values);
	});
	parser->add("Tool settings").add_options()
		("statistics,s", po::bool_switch(&s.collect_statistics), "run tools with statistics")
		("tool", po::value<std::vector<std::filesystem::path>>(&s.tools_generic), "a generic tool")
		("mathsat", po::value<std::vector<std::filesystem::path>>(&s.tools_mathsat), "MathSAT with SMT-LIB interface")
		("minisatp", po::value<std::vector<std::filesystem::path>>(&s.tools_minisatp), "Minisatp with OPB interface")
		("smtrat,S", po::value<std::vector<std::filesystem::path>>(&s.tools_smtrat), "SMT-RAT with SMT-LIB interface")
		("smtrat-opb,O", po::value<std::vector<std::filesystem::path>>(&s.tools_smtrat_opb), "SMT-RAT with OPB interface")
		("z3,Z", po::value<std::vector<std::filesystem::path>>(&s.tools_z3), "z3 with SMT-LIB interface")
	;
}
}

}