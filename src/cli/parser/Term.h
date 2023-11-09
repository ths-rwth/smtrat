#pragma once

#include "Attribute.h"
#include "Common.h"
#include "Lexicon.h"
#include "Identifier.h"
#include "SExpression.h"
#include "Sort.h"
#include "theories/Theories.h"
#include <boost/spirit/home/qi/nonterminal/grammar.hpp>

namespace smtrat {
namespace parser {

struct QualifiedIdentifierParser: public qi::grammar<Iterator, Identifier(), Skipper> {
	QualifiedIdentifierParser(): QualifiedIdentifierParser::base_type(main, "qualified identifier") {
	    main = 
				identifier[qi::_val = qi::_1]
			|	(qi::lit("(") >> "as" >> identifier >> sort >> ")")[qi::_val = px::bind(&QualifiedIdentifierParser::checkQualification, px::ref(*this), qi::_1, qi::_2)]
		;
	}
	
	Identifier checkQualification(const Identifier& identifier, const carl::Sort&) const {
		///@todo Check what can be checked here.
		SMTRAT_LOG_DEBUG("smtrat.parser", "Qualified identifier: " << identifier << " with sort " << sort);
		return identifier;
	}
	
    IdentifierParser identifier;
    SortParser sort;
    qi::rule<Iterator, Identifier(), Skipper> main;
};

struct SortedVariableParser: public qi::grammar<Iterator, std::pair<std::string, carl::Sort>(), Skipper> {
	SortedVariableParser(): SortedVariableParser::base_type(main, "sorted variable") {
		main = qi::lit("(") >> symbol >> sort >> ")";
	}
	SymbolParser symbol;
	SortParser sort;
	qi::rule<Iterator, std::pair<std::string, carl::Sort>(), Skipper> main;
};

struct TermParser: public qi::grammar<Iterator, types::TermType(), Skipper> {
	typedef conversion::VariantVariantConverter<types::TermType> Converter;
	TermParser(Theories* theories): TermParser::base_type(main, "term"), theories(theories) {
		main =
				specconstant[qi::_val = px::bind(&Converter::template convert<types::ConstType>, &converter, qi::_1)]
			|   (qi::lit("(") >> "forall" >> "(" >> (+sortedvariable)[px::bind(&TermParser::declareQuantifiedVariable, px::ref(*this), qi::_1)] >> ")" >> main >> ")")[qi::_val = px::bind(&Theories::quantifiedTerm, px::ref(*theories), qi::_1, qi::_2, true)]
			|   (qi::lit("(") >> "exists" >> "(" >> (+sortedvariable)[px::bind(&TermParser::declareQuantifiedVariable, px::ref(*this), qi::_1)] >> ")" >> main >> ")")[qi::_val = px::bind(&Theories::quantifiedTerm, px::ref(*theories), qi::_1, qi::_2, false)]
			|	qualifiedidentifier[qi::_val = px::bind(&Theories::resolveSymbol, px::ref(*theories), qi::_1)]
			|	(qi::lit("(") >> termop >> ")")[qi::_val = qi::_1]
		;
		termop = 
				(qi::lit("!") >> main >> +attribute)[qi::_val = px::bind(&Theories::annotateTerm, px::ref(*theories), qi::_1, qi::_2)]
			|	(qi::lit("let")[px::bind(&Theories::pushExpressionScope, px::ref(*theories), 1)] >> "(" >> +binding >> ")" >> main[qi::_val = qi::_1])[px::bind(&Theories::popExpressionScope, px::ref(*theories), 1)]
			|	(qualifiedidentifier >> +main)[qi::_val = px::bind(&Theories::functionCall, px::ref(*theories), qi::_1, qi::_2)]
		;
		binding = (qi::lit("(") >> symbol >> main >> ")")[px::bind(&Theories::handleLet, px::ref(*theories), qi::_1, qi::_2)];
	}

	void declareQuantifiedVariable(const std::vector<std::pair<std::string, carl::Sort>>& vars) {
		SMTRAT_LOG_DEBUG("smtrat.parser", "Declare quantified variables: " << vars);
		for(const auto& var: vars) {
			//TODO: It might be that the variable has been declared before -> is this the right way to handle this?
			if(theories->isVariableDeclared(var.first)) continue ;
			theories->declareVariable(var.first, var.second);
		}
	}

	Theories* theories;
	SymbolParser symbol;
	SpecConstantParser specconstant;
	QualifiedIdentifierParser qualifiedidentifier;
	SortedVariableParser sortedvariable;
	AttributeParser attribute;
	Converter converter;
	qi::rule<Iterator, Skipper> binding;
	qi::rule<Iterator, types::TermType(), Skipper> termop;
	qi::rule<Iterator, types::TermType(), Skipper> main;
};

}
}
