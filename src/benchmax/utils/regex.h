/**
 * @file regex.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#ifdef USE_BOOST_REGEX
#include "../cli/config.h"
#ifdef __VS
#pragma warning(push, 0)
#include <boost/regex.hpp>
#pragma warning(pop)
#else
#include <boost/regex.hpp>
#endif
namespace benchmax {
	using boost::regex;
	using boost::regex_match;
	using boost::regex_iterator;
}
#else
#include <stdexcept>
#include <regex>
namespace benchmax {
	using std::regex;
	using std::regex_match;
	using std::sregex_iterator;
}
#endif