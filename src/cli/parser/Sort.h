#pragma once

#include <carl-formula/sort/SortManager.h>

#include "Common.h"
#include "Lexicon.h"
#include "Identifier.h"

namespace smtrat {
namespace parser {

namespace spirit = boost::spirit;
namespace qi = boost::spirit::qi;
namespace px = boost::phoenix;

struct SortParser : public qi::grammar<Iterator, carl::Sort(), Skipper> {
	SortParser(): SortParser::base_type(sort, "sort") {
		sort =
				simpleSort[qi::_val = qi::_1]
			|	parameters[qi::_val = qi::_1]
			|	identifier[qi::_val = px::bind(&SortParser::getSort, px::ref(*this), qi::_1)]
			|	("(" >> identifier >> +sort >> ")")[qi::_val = px::bind(&SortParser::getSortWithParam, px::ref(*this), qi::_1, qi::_2)]
		;
		sort.name("sort");
		Theories::addSimpleSorts(simpleSort);
	}
	
	void setParameters(const std::vector<std::string>& params) {
		for (const auto& p: params) {
			parameters.add(p, carl::getSort(p));
		}
	}
	void clearParameters() {
		parameters.clear();
	}
	
	carl::Sort getSort(const Identifier& i) {
		if (i.indices == nullptr) return carl::getSort(i.symbol);
		return carl::getSort(i.symbol, *i.indices);
	}
	carl::Sort getSortWithParam(const Identifier& i, const std::vector<carl::Sort>& params) {
		if (i.indices == nullptr) return carl::getSort(i.symbol, params);
		return carl::getSort(i.symbol, *i.indices, params);
	}
private:
	SymbolParser symbol;
	IdentifierParser identifier;
	qi::symbols<char, carl::Sort> simpleSort;
	qi::symbols<char, carl::Sort> parameters;
	qi::rule<Iterator, carl::Sort(), Skipper> sort;
};

}
}
