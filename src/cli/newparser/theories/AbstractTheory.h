#pragma once

#include "../Common.h"
#include "TheoryTypes.h"
#include "ParserState.h"

namespace smtrat {
namespace parser {

struct AbstractTheory {
protected:
	ParserState* state;
public:
	AbstractTheory(ParserState* state): state(state) {}

	virtual bool declareVariable(const std::string&, const carl::Sort&) {
		return false;
	}
	virtual bool declareFunction(const std::string&, const std::vector<carl::Sort>&, const carl::Sort&) {
		return false;
	}
	virtual bool defineFunction(const std::string&, const std::vector<carl::Sort>&, const carl::Sort&) {
		return false;
	}

	virtual bool handleITE(const FormulaT&, const types::TermType&, const types::TermType&, types::TermType&, TheoryError& errors) {
		errors.next() << "ITEs are not supported.";
		return false;
	}
	virtual bool handleDistinct(const std::vector<types::TermType>&, types::TermType&, TheoryError& errors) {
		errors.next() << "Distinct is not supported.";
		return false;
	}
	virtual bool functionCall(const Identifier&, const std::vector<types::TermType>&, types::TermType&, TheoryError& errors) {
		errors.next() << "Functions are not supported.";
		return false;
	}
	
	static void addSimpleSorts(qi::symbols<char, carl::Sort>&) {}
	static void addConstants(qi::symbols<char, types::ConstType>&) {}
};

}
}
