#pragma once

#include "../Common.h"
#include "AbstractTheory.h"
#include "ParserState.h"

namespace smtrat {
namespace parser {

/**
 * Implements the theory of arithmetic, including LRA, LIA, NRA and NIA.
 */
struct ArithmeticTheory: public AbstractTheory  {
	using OperatorType = boost::variant<Poly::ConstructorOperation, carl::Relation>;
	
	static void addSimpleSorts(qi::symbols<char, carl::Sort>& sorts);
	
	static bool convertTerm(const types::TermType& term, Poly& result, bool allow_bool = false);
	static bool convertArguments(const OperatorType& op, const std::vector<types::TermType>& arguments, std::vector<Poly>& result, TheoryError& errors);
	
	std::map<std::string, OperatorType> ops;
	std::map<carl::Variable, std::tuple<FormulaT, Poly, Poly>> mITEs;
	
	ArithmeticTheory(ParserState* state);
	
	bool declareVariable(const std::string& name, const carl::Sort& sort, types::VariableType& result, TheoryError& errors);

	bool handleITE(const FormulaT& ifterm, const types::TermType& thenterm, const types::TermType& elseterm, types::TermType& result, TheoryError& errors);
	bool handleDistinct(const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors);
	
	FormulaT makeConstraint(const Poly& lhs, const Poly& rhs, carl::Relation rel);

	bool instantiate(const types::VariableType& var, const types::TermType& replacement, types::TermType& result, TheoryError& errors);
	bool isBooleanIdentity(const OperatorType& op, const std::vector<types::TermType>& arguments, TheoryError& errors);
	bool functionCall(const Identifier& identifier, const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors);
};
	
}
}
