/**
 * @file Tools.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <boost/filesystem/path.hpp>

#ifdef USE_BOOST_REGEX
#include <boost/regex.hpp>
using boost::regex;
using boost::regex_match;
#else
#include <regex>
using std::regex;
using std::regex_match;
#endif

#include "Tool.h"

#include "IsatTool.h"
#include "QepcadTool.h"
#include "RedlogTool.h"
#include "Z3Tool.h"
#include "smtratSolverTool.h"

namespace benchmax {

template<typename T>
void createTools(const std::vector<std::string>& arguments, std::vector<Tool>& tools) {
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
			tools.push_back(T(path, matches[2]));
		}
	}
}

}