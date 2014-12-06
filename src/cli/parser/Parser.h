/**
 * @file Parser.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <cassert>
#include <iostream>
#include <iterator>
#include <list>
#include <stack>

#define BOOST_SPIRIT_USE_PHOENIX_V3

#include <boost/variant.hpp>
#include <boost/fusion/include/std_pair.hpp>
#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/qi_numeric.hpp>
#include <boost/spirit/include/support_line_pos_iterator.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_bind.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>
#include <boost/spirit/include/phoenix_object.hpp>
#include <boost/spirit/include/phoenix_statement.hpp>

#include "../../lib/Common.h"
#include "../../lib/solver/ModuleInput.h"
#include "ParserUtils.h"
#include "ParserTypes.h"

#include "NumberParser.h"
#include "SortParser.h"
#include "UtilityParser.h"
#include "UninterpretedParser.h"

#include "../../lib/logging.h"
#include "ParserState.h"
#include "FunctionArgumentParser.h"
#include "FormulaParser.h"
#include "PolynomialParser.h"

namespace smtrat {
namespace parser {

namespace spirit = boost::spirit;
namespace qi = boost::spirit::qi;
namespace px = boost::phoenix;

template <typename... T>
using rule = qi::rule<Iterator, T()..., Skipper>;

class SMTLIBParser
{
	
private:
	ParserState* state;
	InstructionHandler* handler;
	px::function<SuccessHandler> successHandler;
	px::function<SuccessHandlerPtr> successHandlerPtr;
	px::function<ErrorHandler> errorHandler;
	std::istream* mInputStream;
		
public:
	bool queueInstructions;
		
	// Basic rules
	Skipper skipper;
	KeywordParser keyword;
	SymbolParser symbol;
	DomainParser domain;
	LogicParser logic;
	SortParser sort;
	
	// Numbers
	qi::uint_parser<unsigned,10,1,-1> numeral;
	
	// Variables
	rule<carl::Variable> var;
	rule<std::pair<std::string, carl::Sort>> sortedVar;
	AttributeParser attribute;
	
	// Custom functions
	qi::rule<Iterator, Skipper, qi::locals<std::string, std::vector<carl::Variable>>> fun_definition;

	rule<Arguments> fun_arguments;

	// Commands	
	rule<> cmd;
	
	// Formula
	FormulaParser formula;

	UninterpretedParser uninterpreted;

	// Polynomial
	PolynomialParser polynomial;
	FunctionArgumentParser fun_argument;
	// Main rule
	rule<> main;
	
public:
	
	SMTLIBParser(InstructionHandler* ih, bool queueInstructions, bool debug = false);

	bool parse(std::istream& in, const std::string& filename);

protected:
	void add(FormulaT& f);
	void check();
	void declareConst(const std::string&, const carl::Sort&);
	void declareFun(const std::string& name, const std::vector<carl::Sort>& args, const carl::Sort& sort);
	void declareSort(const std::string&, const unsigned&);
	void defineFun(const std::string&, const std::vector<carl::Variable>&, const carl::Sort&, const Argument&);
	void defineSort(const std::string&, const std::vector<std::string>&, const carl::Sort&);
	void exit();
	void getAssertions();
	void getAssignment();
	void getInfo(const std::string& key);
	void getOption(const std::string& key);
	void getProof();
	void getUnsatCore();
	void getValue(const std::vector<carl::Variable>&);
	void pop(const unsigned&);
	void push(const unsigned&);
	void setInfo(const Attribute& attribute);
	void setLogic(const smtrat::Logic&);
	void setOption(const Attribute& option);
	
	template<typename Function, typename... Args>
	void callHandler(const Function& f, const Args&... args) {
		if (this->queueInstructions) {
			this->handler->addInstruction(std::bind(f, this->handler, args...));
		} else {
			(this->handler->*f)(args...);
		}
	}
	
private:
	
	carl::Variable addQuantifiedVariable(const std::string& _name, const boost::optional<carl::VariableType>& type);
	carl::Variable addVariableBinding(const std::pair<std::string, carl::Sort>&);
	
	void setSortParameters(const std::vector<std::string>& params) {
		for (auto p: params) {
			sort.parameters.add(p, carl::newSort(p));
		}
	}

	void clearSortParameters() {
		sort.parameters.clear();
	}
	void errorMessage(const std::string& msg) {
		std::cerr << "Parser error: " << msg << std::endl;
	}
		
public:
	std::stringstream lastrule;
	std::stringstream lastentity;
	template<typename Rule, typename Entity>
	void lastRule(const Rule& rule, Entity& entity) {
		lastrule.str("");
		lastrule << rule.name();
		lastentity.str("");
		lastentity << entity;
	}
};

}
}