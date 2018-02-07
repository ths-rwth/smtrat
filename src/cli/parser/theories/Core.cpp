#include "Core.h"
#include "ParserState.h"

namespace smtrat {
namespace parser {

	struct CoreInstantiator: public FunctionInstantiator {
		bool operator()(const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors) const {
			std::vector<FormulaT> args;
			if (!convert(arguments, args, errors)) return false;
			return apply(args, result, errors);
		}
		virtual bool apply(const std::vector<FormulaT>& arguments, types::TermType& result, TheoryError& errors) const = 0;
	};
	template<carl::FormulaType type>
	struct NaryCoreInstantiator: public CoreInstantiator {
		bool apply(const std::vector<FormulaT>& arguments, types::TermType& result, TheoryError& ) const {
			result = FormulaT(type, arguments);
			return true;
		}
	};
	struct NotCoreInstantiator: public CoreInstantiator {
		bool apply(const std::vector<FormulaT>& arguments, types::TermType& result, TheoryError& errors) const {
			if (arguments.size() != 1) {
				errors.next() << "Operator \"not\" may only have a single argument.";
				return false;
			}
			result = FormulaT(carl::FormulaType::NOT, arguments[0]);
			return true;
		}
	};
	struct ImpliesCoreInstantiator: public CoreInstantiator {
		bool apply(const std::vector<FormulaT>& arguments, types::TermType& result, TheoryError& errors) const {
			if (arguments.size() != 2) {
				errors.next() << "Operator \"implies\" may only have a single argument.";
				return false;
			}
			result = FormulaT(carl::FormulaType::IMPLIES, {arguments[0], arguments[1]});
			return true;
		}
	};

	void CoreTheory::addSimpleSorts(qi::symbols<char, carl::Sort>& sorts) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		sorts.add("Bool", sm.getInterpreted(carl::VariableType::VT_BOOL));
	}
	void CoreTheory::addConstants(qi::symbols<char, types::ConstType>& constants) {
		constants.add("true", types::ConstType(FormulaT(carl::FormulaType::TRUE)));
		constants.add("false", types::ConstType(FormulaT(carl::FormulaType::FALSE)));
	}

	bool CoreTheory::convertTerm(const types::TermType& term, FormulaT& result) {
		if (boost::get<FormulaT>(&term) != nullptr) {
			result = boost::get<FormulaT>(term);
			return true;
		} else if (boost::get<carl::Variable>(&term) != nullptr) {
			if (boost::get<carl::Variable>(term).type() == carl::VariableType::VT_BOOL) {
				result = FormulaT(boost::get<carl::Variable>(term));
				return true;
			} else {
				return false;
			}
		} else {
			return false;
		}
	}

	bool CoreTheory::convertArguments(const std::vector<types::TermType>& arguments, std::vector<FormulaT>& result, TheoryError& errors) {
		result.clear();
		for (std::size_t i = 0; i < arguments.size(); i++) {
			FormulaT res;
			if (!convertTerm(arguments[i], res)) {
				errors.next() << "Arguments are expected to be formulas, but argument " << (i+1) << " is not: \"" << arguments[i] << "\".";
				return false;
			}
			result.push_back(res);
		}
		return true;
	}

	CoreTheory::CoreTheory(ParserState* state): AbstractTheory(state) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		sm.addInterpretedSort("Bool", carl::VariableType::VT_BOOL);
		
		state->registerFunction("not", new NotCoreInstantiator());
		state->registerFunction("and", new NaryCoreInstantiator<carl::FormulaType::AND>());
		state->registerFunction("iff", new NaryCoreInstantiator<carl::FormulaType::IFF>());
		state->registerFunction("or", new NaryCoreInstantiator<carl::FormulaType::OR>());
		state->registerFunction("xor", new NaryCoreInstantiator<carl::FormulaType::XOR>());
		state->registerFunction("=>", new ImpliesCoreInstantiator());
		state->registerFunction("implies", new ImpliesCoreInstantiator());
	}

	bool CoreTheory::declareVariable(const std::string& name, const carl::Sort& sort, types::VariableType& result, TheoryError& errors) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		switch (sm.getType(sort)) {
			case carl::VariableType::VT_BOOL: {
				assert(state->isSymbolFree(name));
				carl::Variable var = carl::freshVariable(name, carl::VariableType::VT_BOOL);
				state->variables[name] = var;
				result = var;
				return true;
			}
			default:
				errors.next() << "The requested sort was not \"Bool\" but \"" << sort << "\".";
				return false;
		}
	}

	bool CoreTheory::handleITE(const FormulaT& ifterm, const types::TermType& thenterm, const types::TermType& elseterm, types::TermType& result, TheoryError& errors) {
		FormulaT thenf;
		FormulaT elsef;
		if (!convertTerm(thenterm, thenf)) {
			errors.next() << "Failed to construct ITE, the then-term \"" << thenterm << "\" is unsupported.";
			return false;
		}
		if (!convertTerm(elseterm, elsef)) {
			errors.next() << "Failed to construct ITE, the else-term \"" << elseterm << "\" is unsupported.";
			return false;
		}
		result = FormulaT(carl::FormulaType::ITE, {ifterm, thenf, elsef});
		return true;
	}
	bool CoreTheory::handleDistinct(const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors) {
		std::vector<FormulaT> args;
		if (!convertArguments(arguments, args, errors)) return false;
		result = expandDistinct(args, [](const FormulaT& a, const FormulaT& b){
			return FormulaT(carl::FormulaType::XOR, {a, b});
		});
		return true;
	}

	bool CoreTheory::functionCall(const Identifier& identifier, const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors) {
		std::vector<FormulaT> args;
		if (!convertArguments(arguments, args, errors)) return false;
		
		if (boost::iequals(identifier.symbol, "=")) {
			result = FormulaT(carl::FormulaType::IFF, FormulasT(args.begin(), args.end()));
			return true;
		}
		return false;
	}

}
}
