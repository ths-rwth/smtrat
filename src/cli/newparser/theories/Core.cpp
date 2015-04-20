#include "Core.h"
#include "ParserState.h"

namespace smtrat {
namespace parser {

	void CoreTheory::addSimpleSorts(qi::symbols<char, carl::Sort>& sorts) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		sorts.add("Bool", sm.interpretedSort(carl::VariableType::VT_BOOL));
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
			if (boost::get<carl::Variable>(term).getType() == carl::VariableType::VT_BOOL) {
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
				errors.next() << "Arguments are expected to be arithmetic, but argument " << (i+1) << " is not: \"" << arguments[i] << "\".";
				return false;
			}
			result.push_back(res);
		}
		return true;
	}

	CoreTheory::CoreTheory(ParserState* state): AbstractTheory(state) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		sm.interpretedSort("Bool", carl::VariableType::VT_BOOL);
		
		ops.emplace("=", OperatorType(carl::FormulaType::IFF));
		ops.emplace("not", OperatorType(carl::FormulaType::NOT));
		ops.emplace("=>", OperatorType(carl::FormulaType::IMPLIES));
		ops.emplace("and", OperatorType(carl::FormulaType::AND));
		ops.emplace("or", OperatorType(carl::FormulaType::OR));
		ops.emplace("xor", OperatorType(carl::FormulaType::XOR));
	}

	bool CoreTheory::declareVariable(const std::string& name, const carl::Sort& sort) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		if (!sm.isInterpreted(sort)) return false;
		if (sm.interpretedType(sort) != carl::VariableType::VT_BOOL) return false;
		assert(state->isSymbolFree(name));
		state->variables[name] = carl::freshVariable(name, carl::VariableType::VT_BOOL);
		return true;
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
		result = FormulaT(carl::FormulaType::ITE, ifterm, thenf, elsef);
		return true;
	}
	bool CoreTheory::handleDistinct(const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors) {
		std::vector<FormulaT> args;
		if (!convertArguments(arguments, args, errors)) return false;
		FormulasT subformulas;
		for (std::size_t i = 0; i < args.size() - 1; i++) {
			for (std::size_t j = i + 1; j < args.size(); j++) {
				subformulas.insert(FormulaT(carl::FormulaType::XOR, args[i], args[j]));
			}
		}
		result = FormulaT(carl::FormulaType::AND, subformulas);
		return true;
	}

	bool CoreTheory::functionCall(const Identifier& identifier, const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors) {
		std::vector<FormulaT> args;
		auto it = ops.find(identifier);
		if (it == ops.end()) {
			errors.next() << "Invalid operator \"" << identifier << "\".";
			return false;
		}
		OperatorType op = it->second;
		if (!convertArguments(arguments, args, errors)) return false;

		if (boost::get<carl::FormulaType>(&op) != nullptr) {
			carl::FormulaType t = boost::get<carl::FormulaType>(op);
			switch (t) {
				case carl::FormulaType::NOT: {
					if (args.size() == 1) {
						result = FormulaT(t, args[0]);
						return true;
					} else errors.next() << "Operator \"" << op << "\" expects a single argument.";
					break;
				}
				case carl::FormulaType::AND:
				case carl::FormulaType::OR:
				case carl::FormulaType::IFF:
				case carl::FormulaType::XOR: {
					result = FormulaT(t, FormulasT(args.begin(), args.end()));
					return true;
				}
				case carl::FormulaType::IMPLIES: {
					if (args.size() == 2) {
						result = FormulaT(t, args[0], args[1]);
						return true;
					} else errors.next() << "Operator \"" << op << "\" expects two arguments.";
				}
				default: {
					errors.next() << "The operator \"" << op << "\" should never be parsed directly.";
				}
			}
		}
		return false;
	}

}
}
