#pragma once

#define BOOST_SPIRIT_USE_PHOENIX_V3
#include <boost/spirit/include/qi.hpp>

#include "Common.h"
#include "UtilityParser.h"

namespace smtrat {
namespace parser {

namespace spirit = boost::spirit;
namespace qi = boost::spirit::qi;
namespace px = boost::phoenix;

struct SortParser : public qi::grammar<Iterator, carl::Sort(), Skipper> {
    SortParser();
	
	void setParameters(const std::vector<std::string>& params);
	void clearParameters();
private:
    IdentifierParser identifier;
    qi::symbols<char, carl::Sort> simpleSort;
    qi::symbols<char, carl::Sort> parameters;
    qi::rule<Iterator, carl::Sort(), Skipper> sort;
};

}
}