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
	std::map<types::TermType, carl::UVariable> mInstantiatedArguments;
	carl::Sort mBoolSort;
	carl::UVariable mTrue;
	carl::UVariable mFalse;
	
	static bool convertTerm(const types::TermType& term, types::UninterpretedTheory::TermType& result);
	static bool convertArguments(const std::vector<types::TermType>& arguments, std::vector<types::UninterpretedTheory::TermType>& result, TheoryError& errors);
	
	UninterpretedTheory(ParserState* state);
	
	bool declareVariable(const std::string& name, const carl::Sort& sort, types::VariableType& result, TheoryError& errors);
	
	bool handleITE(const FormulaT& ifterm, const types::TermType& thenterm, const types::TermType& elseterm, types::TermType& result, TheoryError& errors);
	
	template<bool negated>
	struct EqualityGenerator: public boost::static_visitor<FormulaT> {
		FormulaT operator()(const carl::UVariable& lhs, const carl::UVariable& rhs) {
			return FormulaT(lhs, rhs, negated);
		}
		FormulaT operator()(const carl::UVariable& lhs, const carl::UFInstance& rhs) {
			return FormulaT(lhs, rhs, negated);
		}
		FormulaT operator()(const carl::UFInstance& lhs, const carl::UVariable& rhs) {
			return FormulaT(lhs, rhs, negated);
		}
		FormulaT operator()(const carl::UFInstance& lhs, const carl::UFInstance& rhs) {
			return FormulaT(lhs, rhs, negated);
		}
	};
	bool handleFunctionInstantiation(const carl::UninterpretedFunction& f, const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors);
	
	bool handleDistinct(const std::vector<types::TermType>&, types::TermType&, TheoryError& errors);
	
	bool functionCall(const Identifier& identifier, const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors);
};
	
}
}
