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
	
	carl::Sort getSort(const Identifier& i) {
		if (i.indices == nullptr) return carl::getSort(i.symbol);
		return carl::getSort(i.symbol, *i.indices);
	}
	carl::Sort getSort(const Identifier& i, const std::vector<carl::Sort>& params) {
		if (i.indices == nullptr) return carl::getSort(i.symbol, params);
		return carl::getSort(i.symbol, *i.indices, params);
	}
private:
	SymbolParser symbol;
	IdentifierParser identifier;
	qi::uint_parser<std::size_t,10,1,-1> numeral;
	qi::symbols<char, carl::Sort> simpleSort;
	qi::symbols<char, carl::Sort> parameters;
	qi::rule<Iterator, carl::Sort(), Skipper> sort;
};

}
}