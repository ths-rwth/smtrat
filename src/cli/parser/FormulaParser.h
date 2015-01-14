/* 
 * @file   FormulaParser.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#define BOOST_SPIRIT_USE_PHOENIX_V3
#include <boost/spirit/include/qi.hpp>

#include "Common.h"
#include "UtilityParser.h"
#include "ParserState.h"
#include "PolynomialParser.h"
#include "UninterpretedParser.h"
#include "FunctionArgumentParser.h"

namespace smtrat {
namespace parser {
	
struct FormulaParser: public qi::grammar<Iterator, FormulaT(), Skipper> {
	FormulaParser(ParserState* state);
	friend class EqualityGenerator;
private:
	ParserState* state;

	FormulaT mkFormula(carl::FormulaType _type, FormulasT& _subformulas);
	FormulaT mkConstraint(const Poly&, const Poly&, carl::Relation);
	FormulaT mkEquality(const Arguments& args);
	FormulaT mkDistinct(const Arguments& args);

	BoundaryParser boundary;
	SymbolParser symbol;
	BooleanOpParser op_bool;
	RelationParser relation;
	DomainParser domain;
	AttributeParser attribute;
	UninterpretedParser uninterpreted;
	PolynomialParser polynomial;
	FunctionArgumentParser fun_argument;
	
	qi::rule<Iterator, qi::unused_type, Skipper, qi::locals<std::string>> binding;
	qi::rule<Iterator, qi::unused_type, Skipper> bindlist;
	qi::rule<Iterator, carl::Variable(), Skipper> quantifiedVar;
	
	qi::rule<Iterator, FormulaT(), Skipper> formula;
	qi::rule<Iterator, FormulaT(), Skipper> formula_op;
	qi::rule<Iterator, FormulasT(), Skipper> formula_list;	
	
};
	
}
}