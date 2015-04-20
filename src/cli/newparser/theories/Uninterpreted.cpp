#include "Uninterpreted.h"
#include "ParserState.h"

namespace smtrat {
namespace parser {

	bool UninterpretedTheory::convertTerm(const types::TermType& term, UninterpretedType& result) {
		if (boost::get<carl::UVariable>(&term) != nullptr) {
			result = boost::get<carl::UVariable>(term);
			return true;
		} else if (boost::get<carl::UFInstance>(&term) != nullptr) {
			result = boost::get<carl::UFInstance>(term);
			return true;
		} else {
			return false;
		}
	}

	bool UninterpretedTheory::convertArguments(const std::string& op, const std::vector<types::TermType>& arguments, std::vector<UninterpretedType>& result, TheoryError& errors) {
		result.clear();
		for (std::size_t i = 0; i < arguments.size(); i++) {
			UninterpretedType res;
			if (!convertTerm(arguments[i], res)) {
				errors.next() << "Operator \"" << op << "\" expects arguments to be uninterpreted, but argument " << (i+1) << " is not: \"" << arguments[i] << "\".";
				return false;
			}
			result.push_back(res);
		}
		return true;
	}

	UninterpretedTheory::UninterpretedTheory(ParserState* state): AbstractTheory(state) {
	}

	bool UninterpretedTheory::declareVariable(const std::string& name, const carl::Sort& sort) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		if (sm.isInterpreted(sort)) return false;
		assert(state->isSymbolFree(name));
		carl::Variable v = carl::freshVariable(name, carl::VariableType::VT_UNINTERPRETED);
		carl::UVariable uv(v, sort);
		state->variables[name] = uv;
		return true;
	}
	bool UninterpretedTheory::declareFunction(const std::string& name, const std::vector<carl::Sort>& args, const carl::Sort& sort) {
		state->declared_functions[name] = carl::newUninterpretedFunction(name, args, sort);
		return true;
	}

	bool UninterpretedTheory::handleITE(const FormulaT& ifterm, const types::TermType& thenterm, const types::TermType& elseterm, types::TermType& result, TheoryError& errors) {
		UninterpretedType thenf;
		UninterpretedType elsef;
		if (!convertTerm(thenterm, thenf)) {
			errors.next() << "Failed to construct ITE, the then-term \"" << thenterm << "\" is unsupported.";
			return false;
		}
		if (!convertTerm(elseterm, elsef)) {
			errors.next() << "Failed to construct ITE, the else-term \"" << elseterm << "\" is unsupported.";
			return false;
		}
		//result = FormulaT(carl::FormulaType::ITE, ifterm, thenf, elsef);
		return true;
	}
	
	bool UninterpretedTheory::handleFunctionInstantiation(const carl::UninterpretedFunction& f, const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors) {
		std::vector<carl::UVariable> vars;
		for (const auto& v: arguments) {
			auto it = state->mUninterpretedArguments.find(v);
			if (it != state->mUninterpretedArguments.end()) {
				vars.push_back(it->second);
				continue;
			} else if (const FormulaT* f = boost::get<FormulaT>(&v)) {
				carl::Variable tmp = carl::freshBooleanVariable();
				vars.push_back(carl::UVariable(tmp));
				state->mGlobalFormulas.insert(FormulaT(carl::FormulaType::IFF, FormulaT(tmp), *f));
			} else if (const Poly* p = boost::get<Poly>(&v)) {
				carl::Variable tmp = carl::freshRealVariable();
				vars.push_back(carl::UVariable(tmp));
				state->mGlobalFormulas.insert(FormulaT(*p - carl::makePolynomial<Poly>(tmp), carl::Relation::EQ));
			} else if (const carl::UVariable* uv = boost::get<carl::UVariable>(&v)) {
				vars.push_back(*uv);
			} else if (const carl::UFInstance* uf = boost::get<carl::UFInstance>(&v)) {
				carl::Variable tmp = carl::freshUninterpretedVariable();
				vars.push_back(carl::UVariable(tmp, uf->uninterpretedFunction().codomain()));
				state->mGlobalFormulas.insert(FormulaT(std::move(carl::UEquality(vars.back(), *uf, false))));
			} else {
				SMTRAT_LOG_ERROR("smtrat.parser", "The function argument type for function " << f << " was invalid.");
				continue;
			}
			state->mUninterpretedArguments[v] = vars.back();
		}
		result = carl::newUFInstance(f, vars);
		return true;
	}

	bool UninterpretedTheory::functionCall(const Identifier& identifier, const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors) {
		auto fit = state->declared_functions.find(identifier.symbol);
		if (fit != state->declared_functions.end()) {
			return handleFunctionInstantiation(fit->second, arguments, result, errors);
		}
		if (identifier.symbol == "=") {
			std::vector<UninterpretedType> args;
			if (!convertArguments(identifier.symbol, arguments, args, errors)) return false;
			FormulasT subformulas;
			EqualityGenerator eg;
			for (std::size_t i = 0; i < args.size() - 1; i++) {
				subformulas.insert(boost::apply_visitor(eg, args[i], args[i+1]));
			}
			result = FormulaT(carl::FormulaType::AND, subformulas);
			return true;
		}
		errors.next() << "Invalid operator \"" << identifier << "\".";
		return false;
	}

}
}
