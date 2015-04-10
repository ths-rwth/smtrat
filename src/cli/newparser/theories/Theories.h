#pragma once

#include "../Common.h"
#include "TheoryTypes.h"
#include "AbstractTheory.h"
#include "ParserState.h"
#include "Core.h"
#include "Arithmetic.h"
#include "Uninterpreted.h"
#ifdef PARSER_BITVECTOR
#include "Bitvector.h"
#endif

namespace smtrat {
namespace parser {

struct Theories {
	
	static void addConstants(qi::symbols<char, types::ConstType>& constants) {
		ArithmeticTheory::addConstants(constants);
#ifdef PARSER_BITVECTOR
		BitvectorTheory::addConstants(constants);
#endif
		CoreTheory::addConstants(constants);
		UninterpretedTheory::addConstants(constants);
	}

	static void addSimpleSorts(qi::symbols<char, carl::Sort>& sorts) {
		ArithmeticTheory::addSimpleSorts(sorts);
#ifdef PARSER_BITVECTOR
		BitvectorTheory::addSimpleSorts(sorts);
#endif
		CoreTheory::addSimpleSorts(sorts);
		UninterpretedTheory::addSimpleSorts(sorts);
	}
	
	Theories(ParserState* state):
		state(state)
	{
		theories.emplace("Arithmetic", new ArithmeticTheory(state));
#ifdef PARSER_BITVECTOR
		theories.emplace("Bitvector", new BitvectorTheory(state));
#endif
		theories.emplace("Core", new CoreTheory(state));
		theories.emplace("Uninterpreted", new UninterpretedTheory(state));
	}
	
	void addGlobalFormulas(FormulasT& formulas) {
		formulas.insert(state->mGlobalFormulas.begin(), state->mGlobalFormulas.end());
		state->mGlobalFormulas.clear();
	}
	void declareVariable(const std::string& name, const carl::Sort& sort) {
		if (state->isSymbolFree(name)) {
			std::cout << "Declaring " << name << " as " << sort << std::endl;
			for (auto& t: theories) {
				if (t.second->declareVariable(name, sort)) return;
			}
			SMTRAT_LOG_ERROR("smtrat.parser", "Variable \"" << name << "\" was declared with an invalid sort \"" << sort << "\".");
		} else {
			SMTRAT_LOG_ERROR("smtrat.parser", "Variable \"" << name << "\" will not be declared due to a name clash.");
		}
	}
	void declareFunction(const std::string& name, const std::vector<carl::Sort>& args, const carl::Sort& sort) {
		if (state->isSymbolFree(name)) {
			state->declared_functions[name] = carl::newUninterpretedFunction(name, args, sort);
		} else {
			SMTRAT_LOG_ERROR("smtrat.parser", "Function \"" << name << "\" will not be declared due to a name clash.");
		}
	}
	
	void declareFunctionArgument(const std::pair<std::string, carl::Sort>& arg) {
		if (state->isSymbolFree(arg.first)) {
			carl::SortManager& sm = carl::SortManager::getInstance();
			if (sm.isInterpreted(arg.second)) {
				carl::Variable v = carl::VariablePool::getInstance().getFreshVariable(arg.first, carl::SortManager::getInstance().getType(arg.second));
				state->bindings.emplace(arg.first, v);
			} else {
				SMTRAT_LOG_ERROR("smtrat.parser", "Function argument \"" << arg.first << "\" is of uninterpreted type.");
			}
		} else {
			SMTRAT_LOG_ERROR("smtrat.parser", "Function argument \"" << arg.first << "\" will not be declared due to a name clash.");
		}
	}
	
	void defineFunction(const std::string& name, const std::vector<std::pair<std::string, carl::Sort>>& arguments, const carl::Sort& sort, const types::TermType& definition) {
		if (state->isSymbolFree(name)) {
			///@todo check that definition matches the sort
			state->defined_functions.emplace(name, new types::UserFunctionInstantiator(arguments, sort, definition));
		} else {
			SMTRAT_LOG_ERROR("smtrat.parser", "Function \"" << name << "\" will not be defined due to a name clash.");
		}
	}

	types::TermType resolveSymbol(const Identifier& identifier) const {
		if (identifier.indices == nullptr) {
			return state->resolveSymbol<types::TermType>(identifier.symbol);
		} else {
			SMTRAT_LOG_ERROR("smtrat.parser", "Indexed symbols are not supported yet.");
			return types::TermType();
		}
	}
	
	void openScope(std::size_t n) {
		for (; n > 0; n--) state->pushScope();
	}
	void closeScope(std::size_t n) {
		for (; n > 0; n--) state->popScope();
	}
	
	void handleLet(const std::string& symbol, const types::TermType& term) {
		state->bindings.emplace(symbol, term);
	}

	types::TermType handleITE(const std::vector<types::TermType>& arguments) {
		types::TermType result;
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
		for (auto& t: theories) {
			if (t.second->handleITE(ifterm, arguments[1], arguments[2], result, te(t.first))) return result;
		}
		SMTRAT_LOG_ERROR("smtrat.parser", "Failed to construct ITE \"" << ifterm << "\" ? \"" << arguments[1] << "\" : \"" << arguments[2] << "\": " << te);
		return result;
	}
	
	types::TermType handleDistinct(const std::vector<types::TermType>& arguments) {
		types::TermType result;
		TheoryError te;
		for (auto& t: theories) {
			if (t.second->handleDistinct(arguments, result, te(t.first))) return result;
		}
		SMTRAT_LOG_ERROR("smtrat.parser", "Failed to construct distinct for \"" << arguments << "\": " << te);
		return result;
	}
	
	types::TermType functionCall(const Identifier& identifier, const std::vector<types::TermType>& arguments) {
		types::TermType result;
		if (identifier.symbol == "ite") {
			if (identifier.indices != nullptr) {
				SMTRAT_LOG_WARN("smtrat.parser", "The function \"" << identifier << "\" should not have indices.");
				return result;
			}
			return handleITE(arguments);
		} else if (identifier.symbol == "distinct") {
			if (identifier.indices != nullptr) {
				SMTRAT_LOG_WARN("smtrat.parser", "The function \"" << identifier << "\" should not have indices.");
				return result;
			}
			return handleDistinct(arguments);
		}
		auto deffunit = state->defined_functions.find(identifier.symbol);
		 if (deffunit != state->defined_functions.end()) {
			if (identifier.indices != nullptr) {
				SMTRAT_LOG_WARN("smtrat.parser", "The function \"" << identifier << "\" should not have indices.");
				return result;
			}
			TheoryError te;
			if ((*deffunit->second)(arguments, result, te)) return result;
			SMTRAT_LOG_ERROR("smtrat.parser", "Failed to call user-defined function \"" << identifier << "\" with arguments " << arguments << ":" << te);
			return result;
		} else {
			TheoryError te;
			for (auto& t: theories) {
				if (t.second->functionCall(identifier, arguments, result, te(t.first))) return result;
			}
			SMTRAT_LOG_ERROR("smtrat.parser", "Failed to call \"" << identifier << "\" with arguments " << arguments << ":" << te);
			return result;
		}
	}
private:
	ParserState* state;
	std::map<std::string, AbstractTheory*> theories;
};
	
}
}
