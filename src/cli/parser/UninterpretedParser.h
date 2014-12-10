/* 
 * @file   UninterpretedParser.h
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
	
	struct UninterpretedParser: public qi::grammar<Iterator, UninterpretedType(), Skipper> {
		UninterpretedParser(ParserState* state, FormulaParser* formula);
	private:
		ParserState* state;

		qi::rule<Iterator, UninterpretedType(), Skipper> uninterpreted;
		
		PolynomialParser polynomial;
		FunctionArgumentParser fun_argument;
	};
	
}
}