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

		BitvectorType createVariable(const carl::BVVariable& bvv) const {
			return BitvectorType(BitvectorPool::getInstance().create(carl::BVTermType::VARIABLE, bvv));
		}
		BitvectorType createUnary(carl::BVTermType type, const BitvectorType& a) const {
			return BitvectorType(BitvectorPool::getInstance().create(type, a));
		}
		BitvectorType createBinary(carl::BVTermType type, const BitvectorType& a, const BitvectorType& b) const {
			return BitvectorType(BitvectorPool::getInstance().create(type, a, b));
		}

		BitvectorUnaryOpParser buop;
		BitvectorBinaryOpParser bbop;
		qi::rule<Iterator, BitvectorType(), Skipper> bitvector;
	};
	
}
}