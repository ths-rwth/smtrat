#pragma once

#include "../Common.h"
#include "AbstractTheory.h"
#include "ParserState.h"

namespace smtrat {
namespace parser {

struct ArithmeticTheory: public AbstractTheory  {
	typedef boost::variant<Poly::ConstructorOperation, carl::Relation> OperatorType;
	
	static void addSimpleSorts(qi::symbols<char, carl::Sort>& sorts);
	
	static bool convertTerm(const types::TermType& term, Poly& result);
	
	static bool convertArguments(const OperatorType& op, const std::vector<types::TermType>& arguments, std::vector<Poly>& result, TheoryError& errors);
	
	std::map<std::string, OperatorType> ops;
	std::map<carl::Variable, std::tuple<FormulaT, Poly, Poly>> mITEs;
	
	ArithmeticTheory(ParserState* state);
	
	bool declareVariable(const std::string& name, const carl::Sort& sort);

	bool handleITE(const FormulaT& ifterm, const types::TermType& thenterm, const types::TermType& elseterm, types::TermType& result, TheoryError& errors);
	
	FormulaT makeConstraint(const Poly& lhs, const Poly& rhs, carl::Relation rel);

	bool functionCall(const Identifier& identifier, const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors);
};
	
}
}
