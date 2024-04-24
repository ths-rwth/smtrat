#pragma once

#include "Common.h"
#include "AbstractTheory.h"
#include "ParserState.h"

namespace smtrat {
namespace parser {
	
namespace arithmetic {
	using OperatorType = boost::variant<Poly::ConstructorOperation, carl::Relation>;
}
/**
 * Implements the theory of arithmetic, including LRA, LIA, NRA and NIA.
 */
struct ArithmeticTheory: public AbstractTheory  {
	static void addSimpleSorts(qi::symbols<char, carl::Sort>& sorts);

	std::map<std::string, arithmetic::OperatorType> ops;
	std::map<carl::Variable, std::tuple<FormulaT, Poly, Poly>> mITEs;
	std::map<carl::Variable, std::tuple<Poly, Poly>> mKnownDivisions;
	std::map<carl::Variable, std::tuple<Poly, Poly>> mNewDivisions;

	ArithmeticTheory(ParserState* state);

	bool declareVariable(const std::string& name, const carl::Sort& sort, types::VariableType& result, TheoryError& errors);

	bool handleITE(const FormulaT& ifterm, const types::TermType& thenterm, const types::TermType& elseterm, types::TermType& result, TheoryError& errors);
	bool handleDistinct(const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors);

	bool instantiate(const types::VariableType& var, const types::TermType& replacement, types::TermType& result, TheoryError& errors);
	bool functionCall(const Identifier& identifier, const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors);

	bool declareQuantifiedTerm(const std::vector<std::pair<std::string, carl::Sort>>& vars, const carl::FormulaType& type, const types::TermType& term, types::TermType& result, TheoryError& errors);

	void handleDivisions();

private:
	std::map<FormulaT, carl::Variable> mappedFormulas;

	bool convertArguments(const arithmetic::OperatorType& op, const std::vector<types::TermType>& arguments, std::vector<Poly>& result, TheoryError& errors);
	bool convertTerm(const types::TermType& term, Poly& result, bool allow_bool = false);

	void addQuantifierToFormula(FormulaT& f);

};

}
}
