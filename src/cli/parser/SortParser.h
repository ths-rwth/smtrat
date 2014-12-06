#pragma once

#define BOOST_SPIRIT_USE_PHOENIX_V3
#include <boost/spirit/include/qi.hpp>

#include "../../lib/Common.h"
#include "ParserTypes.h"
#include "UtilityParser.h"

namespace smtrat {
namespace parser {

namespace spirit = boost::spirit;
namespace qi = boost::spirit::qi;
namespace px = boost::phoenix;

struct SortParser : public qi::grammar<Iterator, carl::Sort(), Skipper> {
    SortParser();
    carl::Sort mkSort(const std::string& name);
    carl::Sort mkSort(const std::string& name, const std::vector<carl::Sort>& parameters);

    IdentifierParser identifier;
    qi::symbols<char, carl::Sort> simpleSort;
    qi::symbols<char, carl::Sort> parameters;
    qi::rule<Iterator, carl::Sort(), Skipper> sort;
};

}
}