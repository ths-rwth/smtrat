#pragma once

#include "../Common.h"
#include "AbstractTheory.h"
#include "ParserState.h"

namespace smtrat {
namespace parser {

struct BitvectorTheory: public AbstractTheory  {
	static bool convertTerm(const types::TermType& term, carl::BVTerm& result);
	static bool convertArguments(const OperatorType& op, const std::vector<types::TermType>& arguments, std::vector<carl::BVTerm>& result, TheoryError& errors);
	
	std::map<std::string, OperatorType> ops;
	
	BitvectorTheory(ParserState* state);
	
	bool declareVariable(const std::string& name, const carl::Sort& sort);
	bool declareFunction(const std::string& name, const std::vector<carl::Sort>& args, const carl::Sort& sort);

	bool handleITE(const FormulaT& ifterm, const types::TermType& thenterm, const types::TermType& elseterm, types::TermType& result, TheoryError& errors);
	
	bool functionCall(const Identifier& identifier, const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors);
};
	
}
}
