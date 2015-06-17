/* 
 * @file   FunctionArgumentParser.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include "../config.h"
#define BOOST_SPIRIT_USE_PHOENIX_V3
#ifdef __VS
#pragma warning(push, 0)
#include <boost/spirit/include/qi.hpp>
#pragma warning(pop)
#else
#include <boost/spirit/include/qi.hpp>
#endif

#include "ParserState.h"

namespace smtrat {
namespace parser {

struct FormulaParser;
struct BitvectorParser;
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
