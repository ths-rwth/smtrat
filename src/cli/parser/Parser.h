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

#include "carl/core/logging.h"

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
	InstructionHandler* handler;
	px::function<SuccessHandler> successHandler;
	px::function<SuccessHandlerPtr> successHandlerPtr;
	px::function<ErrorHandler> errorHandler;
	std::istream* mInputStream;
		
public:
	bool queueInstructions;
	
	DeclaredSymbolParser<carl::Variable> var_bool;
	DeclaredSymbolParser<carl::Variable> var_theory;
	DeclaredSymbolParser<carl::UVariable> var_uninterpreted;
	
	DeclaredSymbolParser<FormulaT> bind_bool;
	DeclaredSymbolParser<Poly> bind_theory;
	DeclaredSymbolParser<UninterpretedType> bind_uninterpreted;
	
	// Basic rules
	Skipper skipper;
	KeywordParser keyword;
	SymbolParser symbol;
	StringParser string;
	RelationParser relation;
	BooleanOpParser op_bool;
	TheoryOpParser op_theory;
	DomainParser domain;
	LogicParser logic;
	SortParser sort;
	
	rule<> boundary;
	
	// Numbers
	qi::uint_parser<unsigned,10,1,-1> numeral;
	IntegralParser integral;
	DecimalParser decimal;
	
	// Variables
	rule<carl::Variable> var;
	rule<carl::Variable> quantifiedVar;
	rule<std::pair<std::string, carl::Sort>> sortedVar;
	rule<Attribute> attribute;
	
	rule<AttributeMandatoryValue> value;
	rule<std::vector<std::string>> symlist;
	rule<> bindlist;
	qi::rule<Iterator, qi::unused_type, Skipper, qi::locals<std::string>> binding;
	
	// Custom functions
	qi::symbols<char, BooleanFunction> funmap_bool;
	qi::symbols<char, TheoryFunction> funmap_theory;
	qi::symbols<char, carl::UninterpretedFunction> funmap_ufbool;
	qi::symbols<char, carl::UninterpretedFunction> funmap_uftheory;
	qi::symbols<char, carl::UninterpretedFunction> funmap_uf;
	qi::rule<Iterator, Skipper, qi::locals<std::string, std::vector<carl::Variable>>> fun_definition;

	rule<Argument> fun_argument;
	rule<Arguments> fun_arguments;

	// Commands	
	rule<> cmd;
	
	// Formula
	rule<FormulaT> formula;
	rule<FormulaT> formula_op;
	rule<std::set<FormulaT>> formula_list;

	rule<UninterpretedType> uninterpreted;

	// Polynomial
	rule<Poly> polynomial;
	rule<std::pair<Poly::ConstructorOperation, std::vector<Poly>>> polynomial_op;
	rule<Poly> polynomial_ite;
	rule<Poly> polynomial_fun;
	rule<Poly> polynomial_uf;
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
	smtrat::Logic mLogic;
	std::set<FormulaT> mTheoryIteBindings;
	std::set<FormulaT> mUninterpretedEqualities;
	std::map<carl::Variable, std::tuple<FormulaT, Poly, Poly>> mTheoryItes;

	struct Scope {
	private:
		qi::symbols<char, carl::Variable> var_bool;
		qi::symbols<char, carl::Variable> var_theory;
		qi::symbols<char, FormulaT> bind_bool;
		qi::symbols<char, Poly> bind_theory;
	public:
		Scope(const SMTLIBParser& parser)
		{
			var_bool = parser.var_bool.sym;
			var_theory = parser.var_theory.sym;
			bind_bool = parser.bind_bool.sym;
			bind_theory = parser.bind_theory.sym;
		}
		void restore(SMTLIBParser& parser) {
			parser.var_bool.sym = this->var_bool;
			parser.var_theory.sym = this->var_theory;
			parser.bind_bool.sym = this->bind_bool;
			parser.bind_theory.sym = this->bind_theory;
		}
	};

	std::stack<Scope> mScopeStack;

	bool isSymbolFree(const std::string& name, bool output = true) {
		std::stringstream out;
		if (name == "true" || name == "false") out << "'" << name << "' is a reserved keyword.";
		else if (this->var_bool.sym.find(name) != nullptr) out << "'" << name << "' has already been defined as a boolean variable.";
		else if (this->var_theory.sym.find(name) != nullptr) out << "'" << name << "' has already been defined as a theory variable.";
		else if (this->var_uninterpreted.sym.find(name) != nullptr) out << "'" << name << "' has already been defined as an uninterpreted variable.";
		else if (this->bind_bool.sym.find(name) != nullptr) out << "'" << name << "' has already been defined as a boolean binding.";
		else if (this->bind_theory.sym.find(name) != nullptr) out << "'" << name << "' has already been defined as a theory binding.";
		else if (this->funmap_bool.find(name) != nullptr) out << "'" << name << "' has already been defined as a boolean function.";
		else if (this->funmap_theory.find(name) != nullptr) out << "'" << name << "' has already been defined as a theory funtion.";
		else if (this->funmap_ufbool.find(name) != nullptr) out << "'" << name << "' has already been defined as an uninterpreted function of boolean return type.";
		else if (this->funmap_uftheory.find(name) != nullptr) out << "'" << name << "' has already been defined as an uninterpreted function of theory return type.";
		else if (this->funmap_uf.find(name) != nullptr) out << "'" << name << "' has already been defined as an uninterpreted function.";
		else return true;
		if (output) this->handler->error() << out.str();
		return false;
	}
	
	void pushScope() {
		mScopeStack.emplace(*this);
	}
	void popScope() {
		mScopeStack.top().restore(*this);
		mScopeStack.pop();
	}
	FormulaT mkConstraint(const Poly&, const Poly&, carl::Relation);
	Poly mkIteInExpr(const FormulaT& _condition, Poly& _then, Poly& _else);
	FormulaT mkFormula(carl::FormulaType _type, std::set<FormulaT>& _subformulas);
	FormulaT mkUFEquality(const UninterpretedType& lhs, const UninterpretedType& rhs);
	
	carl::Variable addQuantifiedVariable(const std::string& _name, const boost::optional<carl::VariableType>& type);
	carl::Variable addVariableBinding(const std::pair<std::string, carl::Sort>&);
	void addTheoryBinding(std::string& _varName, Poly&);
	void addBooleanBinding(std::string&, const FormulaT&);
	void addUninterpretedBinding(std::string&, const UninterpretedType&);

	bool checkArguments(const std::string& name, const std::vector<carl::Variable>& types, const Arguments& args, std::map<carl::Variable, FormulaT>& boolAssignments, std::map<carl::Variable, Poly>& theoryAssignments);
	FormulaT applyBooleanFunction(const BooleanFunction& f, const Arguments& args);
	FormulaT applyUninterpretedBooleanFunction(const carl::UninterpretedFunction& f, const Arguments& args);
	Poly applyTheoryFunction(const TheoryFunction& f, const Arguments& args);
	Poly applyUninterpretedTheoryFunction(const carl::UninterpretedFunction& f, const Arguments& args);
	carl::UFInstance applyUninterpretedFunction(const carl::UninterpretedFunction& f, const Arguments& args);

	void setSortParameters(const std::vector<std::string>& params) {
		for (auto p: params) {
			sort.parameters.add(p, carl::newSort(p));
		}
	}

	void clearSortParameters() {
		sort.parameters.clear();
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