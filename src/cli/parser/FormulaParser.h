/* 
 * @file   FormulaParser.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#define BOOST_SPIRIT_USE_PHOENIX_V3
#include <boost/spirit/include/qi.hpp>

#include "../../lib/Common.h"
#include "UtilityParser.h"
#include "NumberParser.h"
#include "ParserState.h"
#include "PolynomialParser.h"
#include "UninterpretedParser.h"
#include "FunctionArgumentParser.h"

namespace smtrat {
namespace parser {
	
struct FormulaParser: public qi::grammar<Iterator, FormulaT(), Skipper> {
	FormulaParser(ParserState* state);
	
	FormulaT mkFormula(carl::FormulaType _type, std::set<FormulaT>& _subformulas);
	FormulaT mkConstraint(const Poly&, const Poly&, carl::Relation);
	carl::Variable addQuantifiedVariable(const std::string& _name, const boost::optional<carl::VariableType>& type);
	void addTheoryBinding(std::string& _varName, Poly&);
	void addBooleanBinding(std::string&, const FormulaT&);
	void addUninterpretedBinding(std::string&, const UninterpretedType&);
	FormulaT applyBooleanFunction(const BooleanFunction& f, const Arguments& args);
	FormulaT applyUninterpretedBooleanFunction(const carl::UninterpretedFunction& f, const Arguments& args);
	carl::UFInstance applyUninterpretedFunction(const carl::UninterpretedFunction& f, const Arguments& args);
	
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
	qi::rule<Iterator, std::set<FormulaT>(), Skipper> formula_list;	
	
	ParserState* state;
};
	
}
}