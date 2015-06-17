/* 
 * @file   UninterpretedParser.h
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

#include "Common.h"
#include "UtilityParser.h"
#include "ParserState.h"
#include "FunctionArgumentParser.h"
#include "PolynomialParser.h"

namespace smtrat {
namespace parser {
	
	struct FormulaParser;
	
	struct UninterpretedParser: public qi::grammar<Iterator, UninterpretedType(), Skipper> {
		UninterpretedParser(ParserState* state, FormulaParser* formula, BitvectorParser* bitvector);
	private:
		ParserState* state;

		qi::rule<Iterator, UninterpretedType(), Skipper> uninterpreted;
		
		PolynomialParser polynomial;
		FunctionArgumentParser fun_argument;
	};
	
}
}