#pragma once

#include "Common.h"
#include "TheoryTypes.h"
#include "ParserState.h"

#include <boost/spirit/include/qi_symbols.hpp>

namespace smtrat {
namespace parser {

	namespace qi = boost::spirit::qi;

/**
 * Base class for all theories.
 *
 * A theory represents one or multiple SMT-LIB theories and takes care of
 * converting smtlib constructs into our datastructures.
 * 
 * A theory has two kinds of functions:
 * <ul>
 * <li>
 *   Initializer are static functions that initialize global datastructures.
 *   These are for example the set of constants.
 * </li>
 * <li>
 *   Handlers are member functions that implement a certain SMT-LIB functionality.
 *   Handlers always return a boolean that indicates if the theory could complete the request.
 *   Oftentimes, a theory will return false because the request should be handled by another theory.
 *   Handlers are used, whenever the parser can not easily decide which theory to use and thus tries to call every theory.
 *   The result of a handler is always a term that is returned through a reference argument.
 * </li>
 *
 * A theory may override any of the following methods.
 */
struct AbstractTheory {
	ParserState* state;
	
	AbstractTheory(ParserState* state): state(state) {}
	virtual ~AbstractTheory() {}

	/**
	 * Declare a new variable with the given name and the given sort.
	 */
	virtual bool declareVariable(const std::string&, const carl::Sort&, types::VariableType&, TheoryError& errors) {
		errors.next() << "Variable declaration is not supported.";
		return false;
	}
	/**
	 * Resolve a symbol that was not declared within the ParserState.
	 * This might be a symbol that actually uses indices, for example bitvector constants.
	 */
	virtual bool resolveSymbol(const Identifier&, types::TermType&, TheoryError& errors) {
		errors.next() << "Custom symbols are not supported.";
		return false;
	}
	/**
	 * Resolve an if-then-else operator.
	 */
	virtual bool handleITE(const FormulaT&, const types::TermType&, const types::TermType&, types::TermType&, TheoryError& errors) {
		errors.next() << "ITEs are not supported.";
		return false;
	}
	/**
	 * Resolve a distinct operator.
	 */
	virtual bool handleDistinct(const std::vector<types::TermType>&, types::TermType&, TheoryError& errors) {
		errors.next() << "Distinct is not supported.";
		return false;
	}
	template<typename T, typename Builder>
	FormulaT expandDistinct(const std::vector<T>& values, const Builder& neqBuilder) {
		FormulasT subformulas;
		for (std::size_t i = 0; i < values.size() - 1; i++) {
			for (std::size_t j = i + 1; j < values.size(); j++) {
				subformulas.push_back(neqBuilder(values[i], values[j]));
			}
		}
		return FormulaT(carl::FormulaType::AND, subformulas);
	}
	/**
	 * Instantiate a variable within a term.
	 */
	virtual bool instantiate(const types::VariableType&, const types::TermType&, types::TermType&, TheoryError& errors) {
		errors.next() << "Instantiation of arguments is not supported.";
		return false;
	}
	virtual bool refreshVariable(const types::VariableType&, types::VariableType&, TheoryError& errors) {
		errors.next() << "Refreshing variables is not supported.";
		return false;
	}
	/**
	 * Resolve another unknown function call.
	 */
	virtual bool functionCall(const Identifier&, const std::vector<types::TermType>&, types::TermType&, TheoryError& errors) {
		errors.next() << "Functions are not supported.";
		return false;
	}
	
	/**
	 * Initialize the global symbol table for simple sorts.
	 */
	static void addSimpleSorts(qi::symbols<char, carl::Sort>&) {}
	/**
	 * Initialize the global symbol table for constants.
	 */
	static void addConstants(qi::symbols<char, types::ConstType>&) {}
};

}
}
