/* 
 * @file   FunctionArgumentParser.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#define BOOST_SPIRIT_USE_PHOENIX_V3
#include <boost/spirit/include/qi.hpp>

#include "ParserState.h"

namespace smtrat {
namespace parser {

struct FormulaParser;
struct PolynomialParser;
struct BitvectorParser;
struct UninterpretedParser;
	
struct FunctionArgumentParser: public qi::grammar<Iterator, Argument(), Skipper> {
	FunctionArgumentParser(FormulaParser* formula, BitvectorParser* bitvector, UninterpretedParser* uninterpreted, PolynomialParser* polynomial);
private:
	qi::rule<Iterator, Argument(), Skipper> main;
};
	
}
}