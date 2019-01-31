/**
 * @file   RedlogTool.h
 * @author: Sebastian Junges
 * @author: Ulrich Loup
 * @version 2013-04-24
 *
 */

#pragma once

#include "Tool.h"

#include "IsatTool.h"
#include "Minisatp.h"
#include "SMTRAT.h"
#include "SMTRAT_OPB.h"
#include "Z3.h"


#include <benchmax/logging.h>
#include <regex>

namespace benchmax {

using ToolPtr = std::unique_ptr<Tool>;
using Tools = std::vector<ToolPtr>;

template<typename T>
void createTools(const std::vector<std::string>& arguments, Tools& tools) {
	std::regex r("([^ ]+) *(.*)");
	for (const auto& arg: arguments) {
		std::smatch matches;
		if (std::regex_match(arg, matches, r)) {
			fs::path path(matches[1]);
			if (!fs::is_regular_file(path)) {
				BENCHMAX_LOG_WARN("benchmax", "The tool " << path << " does not seem to be a file. We skip it.");
				continue;
			}
			const fs::perms executable = fs::perms::others_exec | fs::perms::group_exec | fs::perms::owner_exec;
			if ((fs::status(path).permissions() & executable) == fs::perms::none) {
				BENCHMAX_LOG_WARN("benchmax", "The tool " << path << " does not seem to be executable. We skip it.");
				continue;
			}
			BENCHMAX_LOG_DEBUG("benchmax.tools", "Adding tool " << path.native() << " with arguments \"" << matches[2] << "\".");
			tools.emplace_back(std::make_unique<T>(path, matches[2]));
		}
	}
}

}
