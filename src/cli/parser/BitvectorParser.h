/* 
 * @file   BitvectorParser.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#define BOOST_SPIRIT_USE_PHOENIX_V3
#include <boost/spirit/include/qi.hpp>

#include "Common.h"
#include "UtilityParser.h"
#include "ParserState.h"
#include "FunctionArgumentParser.h"
#include "PolynomialParser.h"

namespace smtrat {
namespace parser {
	
	struct FormulaParser;
	
	struct BitvectorParser: public qi::grammar<Iterator, BitvectorType(), Skipper> {
		BitvectorParser(ParserState* state);
	private:
		ParserState* state;

		qi::rule<Iterator, BitvectorType(), Skipper> bitvector;
	};
	
}
}