#pragma once

#include "Common.h"
#include "AbstractTheory.h"
#include "ParserState.h"

namespace smtrat {
namespace parser {

/**
 * Implements the theory of bitvectors.
 */
struct BitvectorTheory: public AbstractTheory  {
	carl::Sort bvSort;
	conversion::VectorVariantConverter<types::BVTerm> vectorConverter;
	conversion::VariantConverter<types::BVTerm> termConverter;
	using OperatorType = carl::BVTermType;
	static void addSimpleSorts(qi::symbols<char, carl::Sort>& sorts);
	
	BitvectorTheory(ParserState* state);
	
	bool declareVariable(const std::string& name, const carl::Sort& sort, types::VariableType& result, TheoryError& errors);
	
	bool resolveSymbol(const Identifier& identifier, types::TermType& result, TheoryError& errors);

	bool handleITE(const FormulaT& ifterm, const types::TermType& thenterm, const types::TermType& elseterm, types::TermType& result, TheoryError& errors);
	bool handleDistinct(const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors);
	
	bool instantiate(const types::VariableType& var, const types::TermType& replacement, types::TermType& subject, TheoryError& errors);
	bool refreshVariable(const types::VariableType& var, types::VariableType& subject, TheoryError& errors);
	bool functionCall(const Identifier& identifier, const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors);
};
	
}
}
