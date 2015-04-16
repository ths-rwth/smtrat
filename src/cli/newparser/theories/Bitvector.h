#pragma once

#include "../Common.h"
#include "AbstractTheory.h"
#include "ParserState.h"

namespace smtrat {
namespace parser {

struct BitvectorTheory: public AbstractTheory  {
	carl::Sort bvSort;
	typedef carl::BVTermType OperatorType;
	static void addSimpleSorts(qi::symbols<char, carl::Sort>& sorts);
	static bool convertTerm(const types::TermType& term, types::BVTerm& result);
	static bool convertArguments(const std::vector<types::TermType>& arguments, std::vector<types::BVTerm>& result, TheoryError& errors);
	
	BitvectorTheory(ParserState* state);
	
	bool declareVariable(const std::string& name, const carl::Sort& sort);
	
	bool resolveSymbol(const Identifier& identifier, types::TermType& result, TheoryError& errors);

	bool handleITE(const FormulaT& ifterm, const types::TermType& thenterm, const types::TermType& elseterm, types::TermType& result, TheoryError& errors);
	
	bool functionCall(const Identifier& identifier, const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors);
};
	
}
}
