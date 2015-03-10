/* 
 * @file   PolynomialParser.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <vector>

#define BOOST_SPIRIT_USE_PHOENIX_V3
#include <boost/spirit/include/qi.hpp>

#include "Common.h"
#include "UtilityParser.h"
#include "NumberParser.h"
#include "ParserState.h"
#include "FunctionArgumentParser.h"
#include "BitvectorParser.h"

namespace smtrat {
namespace parser {
	
struct FormulaParser;
	
struct PolynomialParser: public qi::grammar<Iterator, Poly(), Skipper> {
	PolynomialParser(ParserState* state, FormulaParser* formulaPtr, UninterpretedParser* uninterpreted);
private:
	ParserState* state;

	Poly mkIteInExpr(const FormulaT& _condition, Poly& _then, Poly& _else);
    Poly var2Poly(carl::Variable::Arg var) const {
         return carl::makePolynomial<Poly>(var);
    }
    Poly createPoly(const std::pair<Poly::ConstructorOperation, std::vector<Poly>>& p) const {
        return Poly(p);
    }
    Poly rationalToPoly(const smtrat::Rational& rat) const {
        return Poly(rat);
    }

	BoundaryParser boundary;
	TheoryOpParser op_theory;
	IntegralParser integral;
	DecimalParser decimal;
	
	qi::rule<Iterator, Poly(), Skipper> polynomial;
	qi::rule<Iterator, std::pair<Poly::ConstructorOperation, std::vector<Poly>>(), Skipper> polynomial_op;
	qi::rule<Iterator, Poly(), Skipper> polynomial_ite;
	qi::rule<Iterator, Poly(), Skipper> polynomial_fun;
	qi::rule<Iterator, Poly(), Skipper> polynomial_uf;

	BitvectorParser bitvector;
	FunctionArgumentParser fun_argument;
};
	
}
}