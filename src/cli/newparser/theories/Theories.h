#pragma once

#include "../Common.h"
#include "ParserState.h"

#include <carl/util/mpl_utils.h>

#include "Core.h"
#include "Arithmetic.h"

namespace smtrat {
namespace parser {

struct Theories {

	/// Constants
	typedef carl::mpl_concatenate<
			CoreTheory::ConstTypes,
			ArithmeticTheory::ConstTypes
		>::type ConstTypes;
	typedef carl::mpl_variant_of<ConstTypes>::type ConstType;
	
	static void addConstants(qi::symbols<char, ConstType>& constants) {
		CoreTheory::addConstants(constants);
		ArithmeticTheory::addConstants(constants);
	}
	
	typedef carl::mpl_concatenate<
			CoreTheory::ExpressionTypes,
			ArithmeticTheory::ExpressionTypes
		>::type ExpressionTypes;
	typedef carl::mpl_variant_of<ExpressionTypes>::type ExpressionType;
	
	typedef carl::mpl_concatenate<
			CoreTheory::TermTypes,
			ArithmeticTheory::TermTypes
		>::type TermTypes;
	typedef carl::mpl_variant_of<TermTypes>::type TermType;

	static void addSimpleSorts(qi::symbols<char, carl::Sort>& sorts) {
		CoreTheory::addSimpleSorts(sorts);
		ArithmeticTheory::addSimpleSorts(sorts);
	}
	
	Theories(ParserState* state):
		state(state), 
		core(state),
		arithmetic(state)
	{
	}
	
	void addGlobalFormulas(FormulasT& formulas) {
		formulas.insert(state->mGlobalFormulas.begin(), state->mGlobalFormulas.end());
		state->mGlobalFormulas.clear();
	}
	void newVariable(const std::string& name, const carl::Sort& sort) {
		if (state->isSymbolFree(name)) {
			if (core.newVariable(name, sort)) return;
			if (arithmetic.newVariable(name, sort)) return;
			SMTRAT_LOG_ERROR("smtrat.parser", "Variable \"" << name << "\" was declared with an invalid sort \"" << sort << "\".");
		} else {
			SMTRAT_LOG_ERROR("smtrat.parser", "Variable \"" << name << "\" will not be declared due to a name clash.");
		}
	}

	TermType resolveSymbol(const Identifier& identifier) const {
		if (identifier.indices == nullptr) {
			return state->resolveSymbol<TermType>(identifier.symbol);
		} else {
			SMTRAT_LOG_ERROR("smtrat.parser", "Indexed symbols are not supported yet.");
			return TermType();
		}
	}
	
	void openScope() {
		state->pushScope();
	}
	void closeScope() {
		state->popScope();
	}
	
	void handleLet(const std::string& symbol, const TermType& term) {
		TheoryError te;
		if (core.handleLet(symbol, term, te("Core"))) return;
		if (arithmetic.handleLet(symbol, term, te("Arithmetic"))) return;
		SMTRAT_LOG_ERROR("smtrat.parser", "Failed to bind \"" << symbol << "\" to \"" << term << "\":" << te);
		std::cout << "Failed!" << std::endl;
	}

	TermType handleITE(const std::vector<TermType>& arguments) {
		TermType result;
		if (arguments.size() != 3) {
			SMTRAT_LOG_ERROR("smtrat.parser", "Failed to construct ITE expression, only exactly three arguments are allowed, but \"" << arguments << "\" were given.");
			return result;
		}
		if (boost::get<FormulaT>(&arguments[0]) == nullptr) {
			SMTRAT_LOG_ERROR("smtrat.parser", "Failed to construct ITE expression, the first argument must be a formula, but \"" << arguments[0] << "\" was given.");
			return result;
		}
		FormulaT ifterm = boost::get<FormulaT>(arguments[0]);
		if (ifterm.isTrue()) return arguments[1];
		if (ifterm.isFalse()) return arguments[2];
		TheoryError te;
		if (core.handleITE(ifterm, arguments[1], arguments[2], result, te("Core"))) return result;
		if (arithmetic.handleITE(ifterm, arguments[1], arguments[2], result, te("Arithmetic"))) return result;
		SMTRAT_LOG_ERROR("smtrat.parser", "Failed to construct ITE \"" << ifterm << "\" ? \"" << arguments[1] << "\" : \"" << arguments[2] << "\": " << te);
		std::cout << "Failed!" << std::endl;
		return result;
	}
	
	TermType functionCall(const Identifier& identifier, const std::vector<TermType>& arguments) {
		if (identifier.symbol == "ite") {
			return handleITE(arguments);
		}
		TermType result;
		TheoryError te;
		if (core.functionCall(identifier, arguments, result, te("Core"))) return result;
		if (arithmetic.functionCall(identifier, arguments, result, te("Arithmetic"))) return result;
		SMTRAT_LOG_ERROR("smtrat.parser", "Failed to call \"" << identifier << "\" with arguments " << arguments << ":" << te);
		std::cout << "Failed!" << std::endl;
		return result;
	}
private:
	ParserState* state;
	CoreTheory core;
	ArithmeticTheory arithmetic;
};
	
}
}
