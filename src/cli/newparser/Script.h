#pragma once

#include "Common.h"
#include "Attribute.h"
#include "InstructionHandler.h"
#include "Lexicon.h"
#include "Sort.h"
#include "Term.h"

namespace smtrat {
namespace parser {

template<typename Callee>
struct ScriptParser: public qi::grammar<Iterator, Skipper> {
	ScriptParser(InstructionHandler* h, Theories& theories, Callee& callee):
		ScriptParser::base_type(main, "script"),
		handler(h),
		callee(callee),
		state(h),
		theories(theories),
		term(&theories)
	{
		command = qi::lit("(") >> (
				(qi::lit("assert") > term > ")")[px::bind(&Callee::add, px::ref(callee), qi::_1)]
			|	(qi::lit("check-sat") > ")")[px::bind(&Callee::check, px::ref(callee))]
			|	(qi::lit("declare-const") > symbol > sort > ")")[px::bind(&Callee::declareConst, px::ref(callee), qi::_1, qi::_2)]
			|	(qi::lit("declare-fun") > symbol > "(" > *sort > ")" > sort > ")")[px::bind(&Callee::declareFun, px::ref(callee), qi::_1, qi::_2, qi::_3)]
			|	(qi::lit("declare-sort") > symbol > numeral > ")")[px::bind(&Callee::declareSort, px::ref(callee), qi::_1, qi::_2)]
			|	(qi::lit("define-fun") > symbol > "(" > *sortedvariable > ")" > sort > term > ")")
			//|	(qi::lit("define-sort") > symbol > "(" > (*symbol)[px::bind(&SortParser::setParameters, px::ref(sort), qi::_1)] > ")" > sort > ")")[px::bind(&ScriptParser::defineSort, px::ref(callee), qi::_1, qi::_2, qi::_3)]
			|	(qi::lit("exit") > ")")[px::bind(&Callee::exit, px::ref(callee))]
			|	(qi::lit("get-assertions") > ")")[px::bind(&Callee::getAssertions, px::ref(callee))]
			|	(qi::lit("get-assignment") > ")")[px::bind(&Callee::getAssignment, px::ref(callee))]
			|	(qi::lit("get-info") > keyword > ")")[px::bind(&Callee::getInfo, px::ref(callee), qi::_1)]
			|	(qi::lit("get-model") > ")")[px::bind(&Callee::getAssignment, px::ref(callee))]
			|	(qi::lit("get-option") > keyword > ")")[px::bind(&Callee::getOption, px::ref(callee), qi::_1)]
			|	(qi::lit("get-proof") > ")")[px::bind(&Callee::getProof, px::ref(callee))]
			|	(qi::lit("get-unsat-core") > ")")[px::bind(&Callee::getUnsatCore, px::ref(callee))]
			|	(qi::lit("get-value") > +term > ")")[px::bind(&Callee::getValue, px::ref(callee), qi::_1)]
			|	(qi::lit("pop") > (numeral | qi::attr(carl::constant_one<Integer>::get())) > ")")[px::bind(&Callee::pop, px::ref(callee), qi::_1)]
			|	(qi::lit("push") > (numeral | qi::attr(carl::constant_one<Integer>::get())) > ")")[px::bind(&Callee::push, px::ref(callee), qi::_1)]
			|	(qi::lit("set-info") > attribute > ")")[px::bind(&Callee::setInfo, px::ref(callee), qi::_1)]
			|	(qi::lit("set-logic") > symbol > ")")[px::bind(&Callee::setLogic, px::ref(callee), qi::_1)]
			|	(qi::lit("set-option") > attribute > ")")[px::bind(&Callee::setOption, px::ref(callee), qi::_1)]
		);
		main = *command >> qi::eoi;
	}
	
	InstructionHandler* handler;
	Callee& callee;
	ParserState state;
	Theories theories;

	AttributeParser attribute;
	KeywordParser keyword;
	NumeralParser numeral;
	SortParser sort;
	SortedVariableParser sortedvariable;
	SymbolParser symbol;
	TermParser term;
	
	qi::rule<Iterator, Skipper> command;
	qi::rule<Iterator, Skipper> main;
};

}
}
