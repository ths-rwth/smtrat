/**
 * @file   RedlogTool.h
 *         Created on April 14, 2013, 6:10 PM
 * @author: Sebastian Junges
 * @author: Ulrich Loup
 * @version 2013-04-24
 *
 */

#pragma once

#include <boost/filesystem/path.hpp>

#include "Tool.h"

#include "IsatTool.h"
#include "QepcadTool.h"
#include "RedlogTool.h"
#include "Z3.h"
#include "SMTRAT.h"

#include "../utils/regex.h"

namespace benchmax {

template<typename T>
void createTools(const std::vector<std::string>& arguments, std::vector<Tool*>& tools) {
	regex r("([^ ]+)(.*)");
	for (const auto& arg: arguments) {
		std::smatch matches;
		if (regex_match(arg, matches, r)) {
			fs::path path(matches[1]);
			fs::file_status status = fs::status(path);
			if (status.type() != fs::file_type::regular_file) {
				BENCHMAX_LOG_WARN("benchmax", "The tool " << path << " does not seem to be a file. We skip it.");
				continue;
			}
			if ((status.permissions() & (fs::others_exe | fs::group_exe | fs::owner_exe)) == 0) {
				BENCHMAX_LOG_WARN("benchmax", "The tool " << path << " does not seem to be executable. We skip it.");
				continue;
			}
			BENCHMAX_LOG_DEBUG("benchmax.tools", "Adding tool " << path.native());
			tools.push_back(new T(path, matches[2]));
		}
	}
}

}
