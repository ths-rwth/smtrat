#include "Uninterpreted.h"
#include "ParserState.h"
#include "../ParserSettings.h"

#include <carl-formula/uninterpreted/UFInstanceManager.h>

namespace smtrat {
namespace parser {
namespace uninterpreted {

	inline bool convertTerm(const types::TermType& term, types::UTerm& result) {
		if (boost::get<carl::UTerm>(&term) != nullptr) {
			result = boost::get<carl::UTerm>(term);
			return true;
		} else if (boost::get<carl::UVariable>(&term) != nullptr) {
			result = carl::UTerm(boost::get<carl::UVariable>(term));
			return true;
		} else {
			return false;
		}
	}

	inline bool convertArguments(const std::vector<types::TermType>& arguments, std::vector<types::UTerm>& result, TheoryError& errors) {
		result.clear();
		for (std::size_t i = 0; i < arguments.size(); i++) {
			types::UTerm res;
			if (!convertTerm(arguments[i], res)) {
				errors.next() << "Arguments are expected to be uninterpreted, but argument " << (i+1) << " is not: \"" << arguments[i] << "\".";
				return false;
			}
			result.push_back(res);
		}
		return true;
	}
}

	UninterpretedTheory::UninterpretedTheory(ParserState* state):
		AbstractTheory(state), 
		mBoolSort(carl::SortManager::getInstance().addSort("UF_Bool", carl::VariableType::VT_UNINTERPRETED)),
		mTrue(carl::freshVariable("UF_TRUE", carl::VariableType::VT_UNINTERPRETED), mBoolSort),
		mFalse(carl::freshVariable("UF_FALSE", carl::VariableType::VT_UNINTERPRETED), mBoolSort)
	{
		state->artificialVariables.emplace_back(mTrue);
		state->artificialVariables.emplace_back(mFalse);
	}

	bool UninterpretedTheory::declareVariable(const std::string& name, const carl::Sort& sort, types::VariableType& result, TheoryError& errors) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		if (sm.isInterpreted(sort)) {
			errors.next() << "The request sort is not uninterpreted but \"" << sort << "\".";
			return false;
		}
		assert(state->isSymbolFree(name));
		carl::Variable v = carl::freshVariable(name, carl::VariableType::VT_UNINTERPRETED);
		carl::UVariable uv(v, sort);
		state->variables[name] = uv;
		result = uv;
		return true;
	}

	bool UninterpretedTheory::handleITE(const FormulaT& ifterm, const types::TermType& thenterm, const types::TermType& elseterm, types::TermType& result, TheoryError& errors) {
		types::UTerm thent;
		types::UTerm elset;
		if (!uninterpreted::convertTerm(thenterm, thent)) {
			errors.next() << "Failed to construct ITE, the then-term \"" << thenterm << "\" is unsupported.";
			return false;
		}
		if (!uninterpreted::convertTerm(elseterm, elset)) {
			errors.next() << "Failed to construct ITE, the else-term \"" << elseterm << "\" is unsupported.";
			return false;
		}
		if (thent.domain() != elset.domain()) {
			errors.next() << "Failed to construct ITE, the domains of \"" << thent << "\" (" << thent.domain() << ") and \"" << elset << "\" (" << elset.domain() << ") are different.";
			return false;
		}

		carl::Variable var = carl::freshUninterpretedVariable();
		state->artificialVariables.emplace_back(var);
		carl::UVariable uvar(var, thent.domain());
		state->auxiliary_variables.insert(uvar);


		FormulaT consThen(carl::UEquality(carl::UTerm(uvar), thent, false));
		FormulaT consElse(carl::UEquality(carl::UTerm(uvar), elset, false));

		state->global_formulas.emplace_back(FormulaT(carl::FormulaType::IMPLIES, {ifterm, consThen}));
		state->global_formulas.emplace_back(FormulaT(carl::FormulaType::IMPLIES, {!ifterm, consElse}));
		
		result = uvar;
		return true;
	}
	
	bool UninterpretedTheory::handleFunctionInstantiation(const carl::UninterpretedFunction& f, const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError&) {
		std::vector<carl::UTerm> vars;
		for (const auto& v: arguments) {
			auto it = mInstantiatedArguments.find(v);
			if (it != mInstantiatedArguments.end()) {
				vars.push_back(it->second);
				continue;
			} else if (const carl::Variable* var = boost::get<carl::Variable>(&v)) {
				carl::Variable tmp = carl::freshUninterpretedVariable();
				vars.push_back(carl::UTerm(carl::UVariable(tmp, mBoolSort)));
				state->global_formulas.emplace_back(coupleBooleanVariables(*var, carl::UVariable(tmp, mBoolSort)));
			} else if (const FormulaT* formula = boost::get<FormulaT>(&v)) {
				carl::Variable tmp = carl::freshBooleanVariable();
				vars.push_back(carl::UTerm(carl::UVariable(tmp)));
				state->global_formulas.emplace_back(FormulaT(carl::FormulaType::IFF, {FormulaT(tmp), *formula}));
			} else if (const Poly* p = boost::get<Poly>(&v)) {
				carl::Variable tmp = carl::freshRealVariable();
				vars.push_back(carl::UTerm(carl::UVariable(tmp)));
				state->global_formulas.emplace_back(FormulaT(*p - Poly(tmp), carl::Relation::EQ));
			} else if (const carl::UTerm* ut = boost::get<carl::UTerm>(&v)) {
				if (!settings_parser().disable_uf_flattening && ut->isUFInstance()) { // do flattening
					carl::Variable tmp = carl::freshUninterpretedVariable();
					vars.emplace_back(carl::UVariable(tmp, ut->asUFInstance().uninterpretedFunction().codomain()));
					state->global_formulas.emplace_back(FormulaT(carl::UEquality(carl::UTerm(vars.back()), *ut, false)));
				} else {
					vars.push_back(*ut);
				}
			} else if (const carl::UVariable* uv = boost::get<carl::UVariable>(&v)) {
				vars.push_back(carl::UTerm(*uv));
			} else {
				SMTRAT_LOG_ERROR("smtrat.parser", "The function argument type of " << v << " for function " << f << " was invalid.");
				continue;
			}
			mInstantiatedArguments[v] = vars.back();
		}
		carl::UFInstance ufi = carl::newUFInstance(f, vars);
		carl::SortManager& sm = carl::SortManager::getInstance();
		if (sm.isInterpreted(f.codomain())) {
			carl::VariableType type = sm.getType(f.codomain());
			if (type == carl::VariableType::VT_BOOL) {
				SMTRAT_LOG_ERROR("smtrat.parser", "Boolan functions should be abstracted to be of sort " << mBoolSort);
			} else {
				carl::Variable var = carl::freshVariable(type);
				state->global_formulas.emplace_back(FormulaT(carl::UEquality(carl::UVariable(var), ufi, false)));
				result = var;
			}
		} else if (f.codomain() == mBoolSort) {
			carl::UVariable uvar(carl::freshVariable(carl::VariableType::VT_UNINTERPRETED), mBoolSort);
			state->global_formulas.emplace_back(carl::UEquality(carl::UTerm(uvar), carl::UTerm(ufi), false));
			state->global_formulas.push_back(FormulaT(carl::FormulaType::OR, {
				FormulaT(carl::UEquality(carl::UTerm(uvar), carl::UTerm(mTrue), false)),
				FormulaT(carl::UEquality(carl::UTerm(uvar), carl::UTerm(mFalse), false))
			}));
			result = FormulaT(carl::UEquality(carl::UTerm(uvar), carl::UTerm(mTrue), false));
		} else {
			result = carl::UTerm(ufi);
		}
		return true;
	}
	bool UninterpretedTheory::handleDistinct(const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors) {
		std::vector<types::UTerm> args;
		if (!uninterpreted::convertArguments(arguments, args, errors)) return false;
		result = expandDistinct(args, [](const types::UTerm& a, const types::UTerm& b){ 
			return carl::UEquality(a, b, true);
		});
		return true;
	}

	bool UninterpretedTheory::functionCall(const Identifier& identifier, const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors) {
		auto fit = state->declared_functions.find(identifier.symbol);
		if (fit != state->declared_functions.end()) {
			return handleFunctionInstantiation(fit->second, arguments, result, errors);
		}
		if (identifier.symbol == "=") {
			std::vector<types::UTerm> args;
			if (!uninterpreted::convertArguments(arguments, args, errors)) return false;
			FormulasT subformulas;
			for (std::size_t i = 0; i < args.size() - 1; i++) {
				subformulas.emplace_back(carl::UEquality(args[i], args[i+1], false));
			}
			result = FormulaT(carl::FormulaType::AND, subformulas);
			return true;
		}
		errors.next() << "Invalid operator \"" << identifier << "\".";
		return false;
	}

}
}
