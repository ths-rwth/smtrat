#pragma once

#include "Common.h"
#include "AbstractTheory.h"
#include "ParserState.h"

namespace smtrat {
namespace parser {

/**
 * Implements the theory of equalities and uninterpreted functions.
 */
struct UninterpretedTheory: public AbstractTheory {
	std::map<types::TermType, carl::UTerm> mInstantiatedArguments;
	carl::Sort mBoolSort;
	carl::UVariable mTrue;
	carl::UVariable mFalse;
	
	UninterpretedTheory(ParserState* state);

	FormulaT coupleBooleanVariables(carl::Variable v, carl::UVariable uv) {
		return FormulaT(carl::FormulaType::AND, {
			FormulaT(carl::FormulaType::IFF, {FormulaT(v), FormulaT(carl::UEquality(uv, mTrue, false))}),
			FormulaT(carl::FormulaType::IFF, {!FormulaT(v), FormulaT(carl::UEquality(uv, mFalse, false))})
		});
	}
	
	bool declareVariable(const std::string& name, const carl::Sort& sort, types::VariableType& result, TheoryError& errors);
	
	bool handleITE(const FormulaT& ifterm, const types::TermType& thenterm, const types::TermType& elseterm, types::TermType& result, TheoryError& errors);
	bool handleFunctionInstantiation(const carl::UninterpretedFunction& f, const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors);
	
	bool handleDistinct(const std::vector<types::TermType>&, types::TermType&, TheoryError& errors);
	
	bool functionCall(const Identifier& identifier, const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors);
};
	
}
}
