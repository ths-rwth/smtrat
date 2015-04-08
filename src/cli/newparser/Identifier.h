#pragma once

#include "Common.h"
#include "Lexicon.h"

namespace smtrat {
namespace parser {

struct IdentifierParser: public qi::grammar<Iterator, Identifier(), Skipper> {
    IdentifierParser(): IdentifierParser::base_type(main, "identifier") {
	    main = symbol[qi::_val = px::construct<Identifier>(qi::_1)] | indexed;
	    main.name("identifier");
	    indexed = (qi::lit("(") >> qi::lit("_") >> symbol >> +numeral >> qi::lit(")"));//[qi::_val = px::construct<Identifier>(qi::_1, qi::_2)];
	    indexed.name("indexed symbol");
	}
    SymbolParser symbol;
    NumeralParser numeral;
    qi::rule<Iterator, Identifier(), Skipper> main;
    qi::rule<Iterator, Identifier(), Skipper> indexed;
    std::string buildIdentifier(const std::string& name, const std::vector<Integer>& nums) const {
	    assert(nums.size() > 0);
	    std::stringstream ss;
	    ss << name << "|" << nums.front();
	    for (unsigned i = 1; i < nums.size(); i++) ss << "," << nums[i];
	    return ss.str();
	}
};

}
}
