#pragma once

#include "Common.h"
#include "Attribute.h"
#include "InstructionHandler.h"
#include "Lexicon.h"
#include "Sort.h"
#include "Term.h"

namespace smtrat {
namespace parser {

struct LogicParser: public qi::symbols<char, smtrat::Logic> {
	LogicParser() {
		add("QF_BV", smtrat::Logic::QF_BV);
		add("QF_IDL", smtrat::Logic::QF_IDL);
		add("QF_LIA", smtrat::Logic::QF_LIA);
		add("QF_LIRA", smtrat::Logic::QF_LIA);
		add("QF_LRA", smtrat::Logic::QF_LRA);
		add("QF_NIA", smtrat::Logic::QF_NIA);
		add("QF_NIRA", smtrat::Logic::QF_NIA);
		add("QF_NRA", smtrat::Logic::QF_NRA);
		add("QF_PB", smtrat::Logic::QF_PB);
		add("QF_RDL", smtrat::Logic::QF_RDL);
		add("QF_UF", smtrat::Logic::QF_UF);
	}
};
struct ErrorHandler {
	template<typename> struct result { typedef qi::error_handler_result type; };
	template<typename T1, typename T2, typename T3, typename T4>
	qi::error_handler_result operator()(T1 b, T2 e, T3 where, T4 const& what) const {
		auto line_start = spirit::get_line_start(b, where);
		auto line_end = std::find(where, e, '\n');
		std::string line(++line_start, line_end);
	
		SMTRAT_LOG_ERROR("smtrat.parser", "Parsing error at " << spirit::get_line(where) << ":" << spirit::get_column(line_start, where));
		SMTRAT_LOG_ERROR("smtrat.parser", "expected" << std::endl << "\t" << what.tag << ": " << what);
		SMTRAT_LOG_ERROR("smtrat.parser", "but got" << std::endl << "\t" << std::string(where, line_end));
		SMTRAT_LOG_ERROR("smtrat.parser", "in line " << spirit::get_line(where) << std::endl << "\t" << line);
		return qi::fail;
	}
};

struct QuantifierParser: public qi::symbols<char, qe::QuantifierType> {
	QuantifierParser() {
		add("exists", qe::QuantifierType::EXISTS);
		add("forall", qe::QuantifierType::FORALL);
	}
};

struct QEParser: public qi::grammar<Iterator, qe::QEQuery(), Skipper> {
	QEParser(Theories* theories): QEParser::base_type(main, "qe-query"), theories(theories) {
		var = qualifiedidentifier[qi::_val = px::bind(&QEParser::resolveVariable, this, qi::_1)];
		main = +("(" > quantifier > +var > ")");
	}

	carl::Variable resolveVariable(const Identifier& name) const {
		auto v = theories->resolveVariable(name);
		return boost::apply_visitor(carl::overloaded {
			[](carl::Variable v){ return v; },
			[](carl::BVVariable v){ return v.variable(); },
			[](carl::UVariable v){ return v.variable(); },
		}, v);
	}
	
	Theories* theories;
	QualifiedIdentifierParser qualifiedidentifier;
	QuantifierParser quantifier;
	
	qi::rule<Iterator, carl::Variable(), Skipper> var;
	qi::rule<Iterator, qe::QEQuery(), Skipper> main;
};

template<typename Callee>
struct ScriptParser: public qi::grammar<Iterator, Skipper> {
	ScriptParser(InstructionHandler& h, Theories& theories, Callee& callee):
		ScriptParser::base_type(main, "script"),
		handler(h),
		callee(callee),
		state(h),
		theories(theories),
		qeQuery(&theories),
		term(&theories)
	{
		functionDefinitionArg = sortedvariable[qi::_val = px::bind(&Theories::declareFunctionArgument, px::ref(theories), qi::_1)];
		functionDefinition =
			(
				qi::eps[px::bind(&ScriptParser::startFunctionDefinition, px::ref(*this))] > 
				symbol > "(" > *(functionDefinitionArg) > ")" > sort > term > ")" >
				qi::eps[px::bind(&Theories::popScriptScope, px::ref(theories), 1)]
			)[px::bind(&Theories::defineFunction, px::ref(theories), qi::_1, qi::_2, qi::_3, qi::_4)];
		command = qi::lit("(") >> (
				(qi::lit("assert") > term > ")")[px::bind(&Callee::add, px::ref(callee), qi::_1)]
			|	(qi::lit("check-sat") > ")")[px::bind(&Callee::check, px::ref(callee))]
			|	(qi::lit("declare-const") > symbol > sort > ")")[px::bind(&Callee::declareConst, px::ref(callee), qi::_1, qi::_2)]
			|	(qi::lit("declare-fun") > symbol > "(" > *sort > ")" > sort > ")")[px::bind(&Callee::declareFun, px::ref(callee), qi::_1, qi::_2, qi::_3)]
			|	(qi::lit("declare-sort") > symbol > numeral > ")")[px::bind(&Callee::declareSort, px::ref(callee), qi::_1, qi::_2)]
			|	(qi::lit("define-fun") > functionDefinition)
			//|	(qi::lit("define-sort") > symbol > "(" > (*symbol)[px::bind(&SortParser::setParameters, px::ref(sort), qi::_1)] > ")" > sort > ")")[px::bind(&ScriptParser::defineSort, px::ref(callee), qi::_1, qi::_2, qi::_3)]
			|	(qi::lit("echo") > string > ")")[px::bind(&Callee::echo, px::ref(callee), qi::_1)]
			|	(qi::lit("eliminate-quantifiers") > qeQuery > ")")[px::bind(&Callee::eliminateQuantifiers, px::ref(callee), qi::_1)]
			|	(qi::lit("exit") > ")")[px::bind(&Callee::exit, px::ref(callee))]
			|	(qi::lit("get-all-models") > ")")[px::bind(&Callee::getAllModels, px::ref(callee))]
			|	(qi::lit("get-assertions") > ")")[px::bind(&Callee::getAssertions, px::ref(callee))]
			|	(qi::lit("get-assignment") > ")")[px::bind(&Callee::getAssignment, px::ref(callee))]
			|	(qi::lit("get-info") > keyword > ")")[px::bind(&Callee::getInfo, px::ref(callee), qi::_1)]
			|	(qi::lit("get-model") > ")")[px::bind(&Callee::getModel, px::ref(callee))]
			|	(qi::lit("get-option") > keyword > ")")[px::bind(&Callee::getOption, px::ref(callee), qi::_1)]
			|	(qi::lit("get-proof") > ")")[px::bind(&Callee::getProof, px::ref(callee))]
			|	(qi::lit("get-unsat-core") > ")")[px::bind(&Callee::getUnsatCore, px::ref(callee))]
			|	(qi::lit("get-value") > "(" > +term > ")" > ")")[px::bind(&Callee::getValue, px::ref(callee), qi::_1)]
			|	(qi::lit("maximize") > term > ")")[px::bind(&Callee::addObjective, px::ref(callee), qi::_1, OptimizationType::Maximize)]
			|	(qi::lit("minimize") > term > ")")[px::bind(&Callee::addObjective, px::ref(callee), qi::_1, OptimizationType::Minimize)]
			|	(qi::lit("pop") > (numeral | qi::attr(carl::constant_one<Integer>::get())) > ")")[px::bind(&Callee::pop, px::ref(callee), qi::_1)]
			|	(qi::lit("push") > (numeral | qi::attr(carl::constant_one<Integer>::get())) > ")")[px::bind(&Callee::push, px::ref(callee), qi::_1)]
			|	(qi::lit("reset") > ")")[px::bind(&Callee::reset, px::ref(callee))]
			|	(qi::lit("set-info") > attribute > ")")[px::bind(&Callee::setInfo, px::ref(callee), qi::_1)]
			|	(qi::lit("set-logic") > logic > ")")[px::bind(&Callee::setLogic, px::ref(callee), qi::_1)]
			|	(qi::lit("set-option") > attribute > ")")[px::bind(&Callee::setOption, px::ref(callee), qi::_1)]
		);
		main = *command > qi::eoi;
		qi::on_error<qi::fail>(main, errorHandler(qi::_1, qi::_2, qi::_3, qi::_4));
	}
	
	InstructionHandler& handler;
	Callee& callee;
	ParserState state;
	Theories& theories;

	LogicParser logic;
	AttributeParser attribute;
	KeywordParser keyword;
	NumeralParser numeral;
	QEParser qeQuery;
	SortParser sort;
	SortedVariableParser sortedvariable;
	StringParser string;
	SymbolParser symbol;
	TermParser term;
	
	qi::rule<Iterator, types::VariableType(), Skipper> functionDefinitionArg;
	qi::rule<Iterator, Skipper> functionDefinition;
	qi::rule<Iterator, Skipper> command;
	qi::rule<Iterator, Skipper> main;
	
	px::function<ErrorHandler> errorHandler;
	
	void startFunctionDefinition() {
		theories.pushScriptScope(1);
		state.auxiliary_variables.clear();
	}
};

}
}
