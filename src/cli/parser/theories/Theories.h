#pragma once

#include "Attribute.h"
#include "Common.h"
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
#include "BooleanEncoding.h"

#include "../ParserSettings.h"

#include <boost/mpl/for_each.hpp>

namespace smtrat {
namespace parser {

/**
 * The Theories class combines all implemented theories and provides a single interface to interact with all theories at once.
 */
struct Theories {
	
	typedef boost::mpl::vector<
		CoreTheory*
#ifdef PARSER_ENABLE_ARITHMETIC
		, ArithmeticTheory*
#endif
#ifdef PARSER_ENABLE_BITVECTOR
		, BitvectorTheory*
#endif
#ifdef PARSER_ENABLE_UNINTERPRETED
		, UninterpretedTheory*
#endif	
		, BooleanEncodingTheory*
		>::type Modules;
		
		
	Theories(ParserState* state):
		state(state),
		theories()
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
		theories.emplace("BooleanEncoding", new BooleanEncodingTheory(state));
	}
	~Theories() {
		auto it = theories.begin();
		while (it != theories.end()) {
			delete it->second;
			it = theories.erase(it);
		}
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
		formulas.insert(formulas.end(), state->global_formulas.begin(), state->global_formulas.end());
		state->global_formulas.clear();
	}
	void declareVariable(const std::string& name, const carl::Sort& sort) {
		if (state->isSymbolFree(name)) {
			types::VariableType var;
			TheoryError te;
			for (auto& t: theories) {
				if (t.second->declareVariable(name, sort, var, te(t.first))) return;
			}
			SMTRAT_LOG_ERROR("smtrat.parser", "Variable \"" << name << "\" was declared with an invalid sort \"" << sort << "\":" << te);
			HANDLE_ERROR
		} else {
			SMTRAT_LOG_ERROR("smtrat.parser", "Variable \"" << name << "\" will not be declared due to a name clash.");
			HANDLE_ERROR
		}
	}
	void declareFunction(const std::string& name, const std::vector<carl::Sort>& args, const carl::Sort& sort) {
		if (state->isSymbolFree(name)) {
			std::vector<carl::Sort> our_args(args);
			for (auto& a: our_args) {
				if (carl::SortManager::getInstance().getType(a) == carl::VariableType::VT_BOOL) {
					a = carl::SortManager::getInstance().getSort("UF_Bool");
				}
			}
			if (carl::SortManager::getInstance().getType(sort) == carl::VariableType::VT_BOOL) {
				state->declared_functions[name] = carl::newUninterpretedFunction(name, our_args, carl::SortManager::getInstance().getSort("UF_Bool"));
			} else {
				state->declared_functions[name] = carl::newUninterpretedFunction(name, our_args, sort);
			}
		} else {
			SMTRAT_LOG_ERROR("smtrat.parser", "Function \"" << name << "\" will not be declared due to a name clash.");
			HANDLE_ERROR
		}
	}
	
	types::VariableType declareFunctionArgument(const std::pair<std::string, carl::Sort>& arg) {
		if (state->isSymbolFree(arg.first)) {
			TheoryError te;
			types::VariableType result;
			for (auto& t: theories) {
				if (t.second->declareVariable(arg.first, arg.second, result, te(t.first))) return result;
			}
			SMTRAT_LOG_ERROR("smtrat.parser", "Function argument \"" << arg.first << "\" could not be declared:" << te);
			HANDLE_ERROR
		} else {
			SMTRAT_LOG_ERROR("smtrat.parser", "Function argument \"" << arg.first << "\" will not be declared due to a name clash.");
			HANDLE_ERROR
		}
		return types::VariableType(carl::Variable::NO_VARIABLE);
	}
	
	void defineFunction(const std::string& name, const std::vector<types::VariableType>& arguments, const carl::Sort& sort, const types::TermType& definition) {
		if (state->isSymbolFree(name)) {
			///@todo check that definition matches the sort
			if (arguments.size() == 0) {
				state->constants.emplace(name, definition);
			} else {
				SMTRAT_LOG_DEBUG("smtrat.parser", "Defining function \"" << name << "\" as \"" << definition << "\".");
				auto ufi = new UserFunctionInstantiator(arguments, sort, definition, state->auxiliary_variables);
				addGlobalFormulas(ufi->globalFormulas);
				state->registerFunction(name, ufi);
			}
		} else {
			SMTRAT_LOG_ERROR("smtrat.parser", "Function \"" << name << "\" will not be defined due to a name clash.");
			HANDLE_ERROR
		}
	}

	types::TermType resolveSymbol(const Identifier& identifier) const {
		types::TermType result;
		if (settings_parser().disable_theory) return result;
		if (identifier.indices == nullptr) {
			if (state->resolveSymbol(identifier.symbol, result)) return result;
		}
		TheoryError te;
		for (auto& t: theories) {
			if (t.second->resolveSymbol(identifier, result, te(t.first))) return result;
		}
		SMTRAT_LOG_ERROR("smtrat.parser", "Tried to resolve symbol \"" << identifier << "\" which is unknown." << te);
		HANDLE_ERROR
		return types::TermType();
	}
	
	types::VariableType resolveVariable(const Identifier& identifier) const {
		types::VariableType result;
		if (settings_parser().disable_theory) return result;
		if (identifier.indices == nullptr) {
			if (state->resolveSymbol(identifier.symbol, result)) return result;
		}
		HANDLE_ERROR
		return types::VariableType();
	}
	
	void pushExpressionScope(std::size_t n) {
		for (; n > 0; n--) state->pushExpressionScope();
	}
	void popExpressionScope(std::size_t n) {
		for (; n > 0; n--) state->popExpressionScope();
	}
	void pushScriptScope(std::size_t n) {
		for (; n > 0; n--) state->pushScriptScope();
	}
	void popScriptScope(std::size_t n) {
		for (; n > 0; n--) state->popScriptScope();
	}
	
	const auto& annotateTerm(const types::TermType& term, const std::vector<Attribute>& attributes) {
		if (settings_parser().disable_theory) return term;
		FormulaT subject;
		conversion::VariantConverter<FormulaT> converter;
		if (!converter(term, subject)) {
			SMTRAT_LOG_WARN("smtrat.parser", "Ignoring annotation on unsupported expression. We only annotated formulas.");
			return term;
		}
		for (const auto& attr: attributes) {
			if (attr.key == "named") {
				if (carl::variant_is_type<std::string>(attr.value)) {
					const std::string& value = boost::get<std::string>(attr.value);
					SMTRAT_LOG_DEBUG("smtrat.parser", "Naming term: " << value << " = " << term);
					state->handler.annotateName(subject, value);
				} else {
					SMTRAT_LOG_WARN("smtrat.parser", "Ignoring naming with unsupported value type for term " << term);
				}
			} else {
				SMTRAT_LOG_WARN("smtrat.parser", "Ignoring unsupported annotation " << attr << " for term " << term);
			}
		}
		return term;
	}
	
	void handleLet(const std::string& symbol, const types::TermType& term) {
		if (settings_parser().disable_theory) return;
		state->bindings.emplace(symbol, term);
	}

	types::TermType handleITE(const std::vector<types::TermType>& arguments) {
		if (settings_parser().disable_theory) return FormulaT();
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
		if (ifterm.is_true()) return arguments[1];
		if (ifterm.is_false()) return arguments[2];
		TheoryError te;
		for (auto& t: theories) {
			if (t.second->handleITE(ifterm, arguments[1], arguments[2], result, te(t.first))) return result;
		}
		SMTRAT_LOG_ERROR("smtrat.parser", "Failed to construct ITE \"" << ifterm << "\" ? \"" << arguments[1] << "\" : \"" << arguments[2] << "\": " << te);
		HANDLE_ERROR
		return result;
	}
	
	types::TermType handleDistinct(const std::vector<types::TermType>& arguments) {
		if (settings_parser().disable_theory) return FormulaT();
		types::TermType result;
		TheoryError te;
		for (auto& t: theories) {
			if (t.second->handleDistinct(arguments, result, te(t.first))) return result;
		}
		SMTRAT_LOG_ERROR("smtrat.parser", "Failed to construct distinct for \"" << arguments << "\": " << te);
		HANDLE_ERROR
		return result;
	}
	
	bool instantiate(const UserFunctionInstantiator& function, const types::VariableType& var, const types::TermType& repl, types::TermType& subject) {
		if (settings_parser().disable_theory) return true;
		TheoryError errors;
		bool wasInstantiated = false;
		for (auto& t: theories) {
			if (t.second->instantiate(var, repl, subject, errors(t.first))) {
				for (const auto& f: function.globalFormulas) {
					types::TermType tmp = f;
					bool res = t.second->instantiate(var, repl, tmp, errors);
					assert(res);
					state->global_formulas.push_back(boost::get<FormulaT>(tmp));
				}
				wasInstantiated = true;
				break;
			}
		}
		if (!wasInstantiated) {
			SMTRAT_LOG_ERROR("smtrat.parser", "Failed to instantiate function: " << errors);
			HANDLE_ERROR
			return false;
		}
		return true;
	}
	
	bool instantiateUserFunction(const UserFunctionInstantiator& function, const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors) {
		if (settings_parser().disable_theory) {
			result = FormulaT();
			return true;
		}
		if (function.arguments.size() != arguments.size()) {
			errors.next() << "Function was expected to have " << function.arguments.size() << " arguments, but was instantiated with " << arguments.size() << ".";
			return false;
		}
		result = function.definition;
		for (const auto& aux: function.auxiliaries) {
			TheoryError te;
			bool wasRefreshed = false;
			types::VariableType repl;
			for (auto& t: theories) {
				if (t.second->refreshVariable(aux, repl, te(t.first))) {
					wasRefreshed = true;
					break;
				}
			}
			if (!wasRefreshed) {
				SMTRAT_LOG_ERROR("smtrat.parser", "Failed to refresh auxiliary variable \"" << aux << "\": " << te);
				HANDLE_ERROR
				return false;
			}
			if (!instantiate(function, aux, repl, result)) return false;
		}
		for (std::size_t i = 0; i < arguments.size(); i++) {
			if (!instantiate(function, function.arguments[i], arguments[i], result)) return false;
		}
		return true;
	}
	
	types::TermType functionCall(const Identifier& identifier, const std::vector<types::TermType>& arguments) {
		if (settings_parser().disable_theory) return FormulaT();
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
		auto udeffunit = state->defined_user_functions.find(identifier.symbol);
		if (udeffunit != state->defined_user_functions.end()) {
			if (identifier.indices != nullptr) {
				SMTRAT_LOG_ERROR("smtrat.parser", "The function \"" << identifier << "\" should not have indices.");
				HANDLE_ERROR
				return result;
			}
			SMTRAT_LOG_DEBUG("smtrat.parser", "Trying to call function \"" << identifier << "\" with arguments " << arguments << ".");
			if (instantiateUserFunction(*udeffunit->second, arguments, result, te(identifier.symbol))) {
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
