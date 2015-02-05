#include "SortParser.h"

#include <boost/spirit/include/phoenix_bind.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>

namespace smtrat {
namespace parser {

	SortParser::SortParser(): SortParser::base_type(sort, "sort") {
		sort =
				simpleSort[qi::_val = qi::_1]
			|	parameters[qi::_val = qi::_1]
			|	identifier[qi::_val = px::bind(&SortParser::getSort, px::ref(*this), qi::_1)]
			|	("(" >> identifier >> +sort >> ")")[qi::_val = px::bind(&SortParser::getSort, px::ref(*this), qi::_1, qi::_2)]
		;
		sort.name("sort");
		simpleSort.add("Bool", carl::SortManager::getInstance().interpretedSort("Bool", carl::VariableType::VT_BOOL));
		simpleSort.add("Int", carl::SortManager::getInstance().interpretedSort("Int", carl::VariableType::VT_INT));
		simpleSort.add("Real", carl::SortManager::getInstance().interpretedSort("Real", carl::VariableType::VT_REAL));
	}
	
	void SortParser::setParameters(const std::vector<std::string>& params) {
		for (const auto& p: params) {
			parameters.add(p, carl::getSort(p));
		}
	}

	void SortParser::clearParameters() {
		parameters.clear();
	}
}
}