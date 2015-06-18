/**
 * @file regex.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#ifdef USE_BOOST_REGEX
#include <boost/regex.hpp>
namespace benchmax {
	using boost::regex;
	using boost::regex_match;
	using boost::smatch;
	using boost::regex_iterator;
}
#else
#include <stdexcept>
#include <regex>
namespace benchmax {
	using std::regex;
	using std::regex_match;
	using std::smatch;
	using regex_iterator = std::sregex_iterator;
}
#endif
