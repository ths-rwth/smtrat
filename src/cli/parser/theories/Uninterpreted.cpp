#include "Uninterpreted.h"
#include "ParserState.h"

namespace smtrat {
namespace parser {
namespace uninterpreted {

	inline bool convertTerm(const types::TermType& term, types::UninterpretedTheory::TermType& result) {
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

	inline bool convertArguments(const std::vector<types::TermType>& arguments, std::vector<types::UninterpretedTheory::TermType>& result, TheoryError& errors) {
		result.clear();
		for (std::size_t i = 0; i < arguments.size(); i++) {
			types::UninterpretedTheory::TermType res;
			if (!convertTerm(arguments[i], res)) {
				errors.next() << "Arguments are expected to be uninterpreted, but argument " << (i+1) << " is not: \"" << arguments[i] << "\".";
				return false;
			}
			result.push_back(res);
		}
		return true;
	}
	
	template<bool negated>
	struct EqualityGenerator: public boost::static_visitor<FormulaT> {
		FormulaT operator()(const carl::UVariable& lhs, const carl::UVariable& rhs) {
			return FormulaT(lhs, rhs, negated);
		}
		FormulaT operator()(const carl::UVariable& lhs, const carl::UFInstance& rhs) {
			return FormulaT(lhs, rhs, negated);
		}
		FormulaT operator()(const carl::UFInstance& lhs, const carl::UVariable& rhs) {
			return FormulaT(lhs, rhs, negated);
		}
		FormulaT operator()(const carl::UFInstance& lhs, const carl::UFInstance& rhs) {
			return FormulaT(lhs, rhs, negated);
		}
	};
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

	bool UninterpretedTheory::handleITE(const FormulaT&, const types::TermType& thenterm, const types::TermType& elseterm, types::TermType&, TheoryError& errors) {
		types::UninterpretedTheory::TermType thenf;
		types::UninterpretedTheory::TermType elsef;
		if (!uninterpreted::convertTerm(thenterm, thenf)) {
			errors.next() << "Failed to construct ITE, the then-term \"" << thenterm << "\" is unsupported.";
			return false;
		}
		if (!uninterpreted::convertTerm(elseterm, elsef)) {
			errors.next() << "Failed to construct ITE, the else-term \"" << elseterm << "\" is unsupported.";
			return false;
		}
		//result = FormulaT(carl::FormulaType::ITE, ifterm, thenf, elsef);
		return false;
	}
	
	bool UninterpretedTheory::handleFunctionInstantiation(const carl::UninterpretedFunction& f, const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError&) {
		std::vector<carl::UVariable> vars;
		for (const auto& v: arguments) {
			auto it = mInstantiatedArguments.find(v);
			if (it != mInstantiatedArguments.end()) {
				vars.push_back(it->second);
				continue;
			} else if (const FormulaT* f = boost::get<FormulaT>(&v)) {
				carl::Variable tmp = carl::freshBooleanVariable();
				vars.push_back(carl::UVariable(tmp));
				state->global_formulas.emplace_back(FormulaT(carl::FormulaType::IFF, {FormulaT(tmp), *f}));
			} else if (const Poly* p = boost::get<Poly>(&v)) {
				carl::Variable tmp = carl::freshRealVariable();
				vars.push_back(carl::UVariable(tmp));
				state->global_formulas.emplace_back(FormulaT(*p - carl::makePolynomial<Poly>(tmp), carl::Relation::EQ));
			} else if (const carl::UVariable* uv = boost::get<carl::UVariable>(&v)) {
				vars.push_back(*uv);
			} else if (const carl::UFInstance* uf = boost::get<carl::UFInstance>(&v)) {
				carl::Variable tmp = carl::freshUninterpretedVariable();
				vars.push_back(carl::UVariable(tmp, uf->uninterpretedFunction().codomain()));
				state->global_formulas.emplace_back(FormulaT(carl::UEquality(vars.back(), *uf, false)));
			} else {
				SMTRAT_LOG_ERROR("smtrat.parser", "The function argument type for function " << f << " was invalid.");
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
			state->global_formulas.emplace_back(carl::UEquality(uvar, ufi, false));
			state->global_formulas.push_back(FormulaT(carl::FormulaType::OR, {
				FormulaT(carl::UEquality(uvar, mTrue, false)),
				FormulaT(carl::UEquality(uvar, mFalse, false))
			}));
			result = FormulaT(carl::UEquality(uvar, mTrue, false));
		} else {
			result = ufi;
		}
		return true;
	}
	bool UninterpretedTheory::handleDistinct(const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors) {
		std::vector<types::UninterpretedTheory::TermType> args;
		if (!uninterpreted::convertArguments(arguments, args, errors)) return false;
		uninterpreted::EqualityGenerator<true> eg;
		result = expandDistinct(args, [&eg](const types::UninterpretedTheory::TermType& a, const types::UninterpretedTheory::TermType& b){ 
			return boost::apply_visitor(eg, a, b); 
		});
		return true;
	}

	bool UninterpretedTheory::functionCall(const Identifier& identifier, const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors) {
		auto fit = state->declared_functions.find(identifier.symbol);
		if (fit != state->declared_functions.end()) {
			return handleFunctionInstantiation(fit->second, arguments, result, errors);
		}
		if (identifier.symbol == "=") {
			std::vector<types::UninterpretedTheory::TermType> args;
			if (!uninterpreted::convertArguments(arguments, args, errors)) return false;
			FormulasT subformulas;
			uninterpreted::EqualityGenerator<false> eg;
			for (std::size_t i = 0; i < args.size() - 1; i++) {
				subformulas.push_back(boost::apply_visitor(eg, args[i], args[i+1]));
			}
			result = FormulaT(carl::FormulaType::AND, subformulas);
			return true;
		}
		errors.next() << "Invalid operator \"" << identifier << "\".";
		return false;
	}

}
}
