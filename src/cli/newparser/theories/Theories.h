#pragma once

#include "../Common.h"
#include "TheoryTypes.h"
#include "AbstractTheory.h"
#include "ParserState.h"
#include "Core.h"
#include "Arithmetic.h"
#ifdef PARSER_ENABLE_BITVECTOR
#include "Bitvector.h"
#endif
#ifdef PARSER_ENABLE_UNINTERPRETED
#include "Uninterpreted.h"
#endif

namespace smtrat {
namespace parser {

/**
 * The Theories class combines all implemented theories and provides a single interface to interact with all theories at once.
 */
struct Theories {
	
	typedef boost::mpl::vector<
		CoreTheory*,
#ifdef PARSER_ENABLE_ARITHMETIC
		ArithmeticTheory*,
#endif
#ifdef PARSER_ENABLE_BITVECTOR
		BitvectorTheory*,
#endif
#ifdef PARSER_ENABLE_UNINTERPRETED
		UninterpretedTheory*
#endif	
		>::type Modules;
		
		
	Theories(ParserState* state):
		state(state)
	{
		theories.emplace("Core", new CoreTheory(state));
#ifdef PARSER_ENABLE_ARITHMETIC
		theories.emplace("Arithmetic", new ArithmeticTheory(state));
#endif
#ifdef PARSER_ENABLE_BITVECTOR
		theories.emplace("Bitvector", new BitvectorTheory(state));
#endif
#ifdef PARSER_ENABLE_UNINTERPRETED
		theories.emplace("Uninterpreted", new UninterpretedTheory(state));
#endif	
	}
	
	/**
	 * Helper functor for addConstants() method.
	 */
	struct ConstantAdder {
		qi::symbols<char, types::ConstType>& constants;
		ConstantAdder(qi::symbols<char, types::ConstType>& constants): constants(constants) {}
		template<typename T> void operator()(T*) {
			T::addConstants(constants);
		}
	};
	/**
	 * Collects constants from all theory modules.
	 */
	static void addConstants(qi::symbols<char, types::ConstType>& constants) {
		boost::mpl::for_each<Modules>(ConstantAdder(constants));
	}

	/**
	 * Helper functor for addSimpleSorts() method.
	 */
	struct SimpleSortAdder {
		qi::symbols<char, carl::Sort>& sorts;
		SimpleSortAdder(qi::symbols<char, carl::Sort>& sorts): sorts(sorts) {}
		template<typename T> void operator()(T*) {
			T::addSimpleSorts(sorts);
		}
	};
	/**
	 * Collects simple sorts from all theory modules.
	 */
	static void addSimpleSorts(qi::symbols<char, carl::Sort>& sorts) {
		boost::mpl::for_each<Modules>(SimpleSortAdder(sorts));
	}
	
	void addGlobalFormulas(FormulasT& formulas) {
		formulas.insert(state->mGlobalFormulas.begin(), state->mGlobalFormulas.end());
		state->mGlobalFormulas.clear();
	}
	void declareVariable(const std::string& name, const carl::Sort& sort) {
		if (state->isSymbolFree(name)) {
			for (auto& t: theories) {
				if (t.second->declareVariable(name, sort)) return;
			}
			SMTRAT_LOG_ERROR("smtrat.parser", "Variable \"" << name << "\" was declared with an invalid sort \"" << sort << "\".");
			HANDLE_ERROR
		} else {
			SMTRAT_LOG_ERROR("smtrat.parser", "Variable \"" << name << "\" will not be declared due to a name clash.");
			HANDLE_ERROR
		}
	}
	void declareFunction(const std::string& name, const std::vector<carl::Sort>& args, const carl::Sort& sort) {
		if (state->isSymbolFree(name)) {
			state->declared_functions[name] = carl::newUninterpretedFunction(name, args, sort);
		} else {
			SMTRAT_LOG_ERROR("smtrat.parser", "Function \"" << name << "\" will not be declared due to a name clash.");
			HANDLE_ERROR
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
				HANDLE_ERROR
			}
		} else {
			SMTRAT_LOG_ERROR("smtrat.parser", "Function argument \"" << arg.first << "\" will not be declared due to a name clash.");
			HANDLE_ERROR
		}
	}
	
	void defineFunction(const std::string& name, const std::vector<std::pair<std::string, carl::Sort>>& arguments, const carl::Sort& sort, const types::TermType& definition) {
		if (state->isSymbolFree(name)) {
			///@todo check that definition matches the sort
			if (arguments.size() == 0) {
				state->defined_constants.emplace(name, definition);
			} else {
				state->defined_functions.emplace(name, new UserFunctionInstantiator(arguments, sort, definition));
			}
		} else {
			SMTRAT_LOG_ERROR("smtrat.parser", "Function \"" << name << "\" will not be defined due to a name clash.");
			HANDLE_ERROR
		}
	}

	types::TermType resolveSymbol(const Identifier& identifier) const {
		types::TermType result;
		if (identifier.indices == nullptr) {
			if (state->resolveSymbol(identifier.symbol, result)) return result;
		}
		TheoryError te;
		for (auto& t: theories) {
			if (t.second->resolveSymbol(identifier, result, te)) return result;
		}
		SMTRAT_LOG_ERROR("smtrat.parser", "Tried to resolve symbol \"" << identifier << "\" which is unknown." << te);
		HANDLE_ERROR
		return types::TermType();
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
			HANDLE_ERROR
			return result;
		}
		FormulaT ifterm;
		conversion::VariantConverter<FormulaT> converter;
		if (!converter(arguments[0], ifterm)) {
			SMTRAT_LOG_ERROR("smtrat.parser", "Failed to construct ITE expression, the first argument must be a formula, but \"" << arguments[0] << "\" was given.");
			HANDLE_ERROR
			return result;
		}
		if (ifterm.isTrue()) return arguments[1];
		if (ifterm.isFalse()) return arguments[2];
		TheoryError te;
		for (auto& t: theories) {
			if (t.second->handleITE(ifterm, arguments[1], arguments[2], result, te(t.first))) return result;
		}
		SMTRAT_LOG_ERROR("smtrat.parser", "Failed to construct ITE \"" << ifterm << "\" ? \"" << arguments[1] << "\" : \"" << arguments[2] << "\": " << te);
		HANDLE_ERROR
		return result;
	}
	
	types::TermType handleDistinct(const std::vector<types::TermType>& arguments) {
		types::TermType result;
		TheoryError te;
		for (auto& t: theories) {
			if (t.second->handleDistinct(arguments, result, te(t.first))) return result;
		}
		SMTRAT_LOG_ERROR("smtrat.parser", "Failed to construct distinct for \"" << arguments << "\": " << te);
		HANDLE_ERROR
		return result;
	}
	
	types::TermType functionCall(const Identifier& identifier, const std::vector<types::TermType>& arguments) {
		types::TermType result;
		TheoryError te;
		if (identifier.symbol == "ite") {
			if (identifier.indices != nullptr) {
				SMTRAT_LOG_ERROR("smtrat.parser", "The function \"" << identifier << "\" should not have indices.");
				HANDLE_ERROR
				return result;
			}
			return handleITE(arguments);
		} else if (identifier.symbol == "distinct") {
			if (identifier.indices != nullptr) {
				SMTRAT_LOG_ERROR("smtrat.parser", "The function \"" << identifier << "\" should not have indices.");
				HANDLE_ERROR
				return result;
			}
			return handleDistinct(arguments);
		}
		auto deffunit = state->defined_functions.find(identifier.symbol);
		if (deffunit != state->defined_functions.end()) {
			if (identifier.indices != nullptr) {
				SMTRAT_LOG_ERROR("smtrat.parser", "The function \"" << identifier << "\" should not have indices.");
				HANDLE_ERROR
				return result;
			}
			SMTRAT_LOG_DEBUG("smtrat.parser", "Trying to call function \"" << identifier << "\" with arguments " << arguments << ".");
			if ((*deffunit->second)(arguments, result, te(identifier.symbol))) {
				SMTRAT_LOG_DEBUG("smtrat.parser", "Success, result is \"" << result << "\".");
				return result;
			}
			SMTRAT_LOG_ERROR("smtrat.parser", "Failed to call function \"" << identifier << "\" with arguments " << arguments << ":" << te);
			HANDLE_ERROR
			return result;
		}
		auto ideffunit = state->defined_indexed_functions.find(identifier.symbol);
		if (ideffunit != state->defined_indexed_functions.end()) {
			if (identifier.indices == nullptr) {
				SMTRAT_LOG_ERROR("smtrat.parser", "The function \"" << identifier << "\" should have indices.");
				HANDLE_ERROR
				return result;
			}
			SMTRAT_LOG_DEBUG("smtrat.parser", "Trying to call function \"" << identifier << "\" with arguments " << arguments << ".");
			if ((*ideffunit->second)(*identifier.indices, arguments, result, te(identifier.symbol))) {
				SMTRAT_LOG_DEBUG("smtrat.parser", "Success, result is \"" << result << "\".");
				return result;
			}
			SMTRAT_LOG_ERROR("smtrat.parser", "Failed to call function \"" << identifier << "\" with arguments " << arguments << ":" << te);
			HANDLE_ERROR
			return result;
		}
		for (auto& t: theories) {
			if (t.second->functionCall(identifier, arguments, result, te(t.first))) return result;
		}
		SMTRAT_LOG_ERROR("smtrat.parser", "Failed to call \"" << identifier << "\" with arguments " << arguments << ":" << te);
		HANDLE_ERROR
		return result;
	}
private:
	ParserState* state;
	std::map<std::string, AbstractTheory*> theories;
};
	
}
}
