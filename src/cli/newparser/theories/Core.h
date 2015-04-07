#pragma once

#include "../Common.h"
#include "ParserState.h"

namespace smtrat {
namespace parser {

struct CoreTheory {
	typedef mpl::vector<FormulaT, std::string> ConstTypes;
	typedef mpl::vector<FormulaT, std::string> ExpressionTypes;
	typedef mpl::vector<FormulaT, std::string> TermTypes;
	typedef carl::mpl_variant_of<TermTypes>::type TermType;
	typedef boost::variant<carl::FormulaType> OperatorType;
	
	static void addSimpleSorts(qi::symbols<char, carl::Sort>& sorts) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		sorts.add("Bool", sm.interpretedSort(carl::VariableType::VT_BOOL));
	}
	template<typename T>
	static void addConstants(qi::symbols<char, T>& constants) {
		constants.add("true", T(FormulaT(carl::FormulaType::TRUE)));
		constants.add("false", T(FormulaT(carl::FormulaType::FALSE)));
	}
	
	template<typename Term>
	static bool convertTerm(const Term& term, FormulaT& result) {
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
	
	template<typename Operator, typename Term>
	static bool convertArguments(const Operator& op, const std::vector<Term>& arguments, std::vector<FormulaT>& result, TheoryError& errors) {
		result.clear();
		for (std::size_t i = 0; i < arguments.size(); i++) {
			FormulaT res;
			if (!convertTerm(arguments[i], res)) {
				errors.next() << "Operator \"" << op << "\" expects arguments to be arithmetic, but argument " << (i+1) << " is not: \"" << arguments[i] << "\".";
				return false;
			}
			result.push_back(res);
		}
		return true;
	}
	
	ParserState* state;
	std::map<std::string, OperatorType> ops;
	CoreTheory(ParserState* state): state(state) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		sm.interpretedSort("Bool", carl::VariableType::VT_BOOL);
		
		ops.emplace("=", OperatorType(carl::FormulaType::IFF));
		ops.emplace("not", OperatorType(carl::FormulaType::NOT));
		ops.emplace("=>", OperatorType(carl::FormulaType::IMPLIES));
		ops.emplace("and", OperatorType(carl::FormulaType::AND));
		ops.emplace("or", OperatorType(carl::FormulaType::OR));
		ops.emplace("xor", OperatorType(carl::FormulaType::XOR));
	}
	
	bool newVariable(const std::string& name, const carl::Sort& sort) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		if (!sm.isInterpreted(sort)) return false;
		if (sm.interpretedType(sort) != carl::VariableType::VT_BOOL) return false;
		assert(state->isSymbolFree(name));
		state->var_bool[name] = carl::freshVariable(name, carl::VariableType::VT_BOOL);
		return true;
	}

	template<typename Term>
	bool handleLet(const std::string& symbol, const Term& term, TheoryError& errors) {
		if (boost::get<FormulaT>(&term) != nullptr) {
			state->bind_bool.emplace(symbol, boost::get<FormulaT>(term));
		} else if (boost::get<carl::Variable>(&term) != nullptr) {
			if (boost::get<carl::Variable>(term).getType() == carl::VariableType::VT_BOOL) {
				state->bind_bool.emplace(symbol, FormulaT(boost::get<carl::Variable>(term)));
			} else {
				errors.next() << "Failed to bind \"" << symbol << "\" to a non-boolean variable.";
				return false;
			}
		} else {
			errors.next() << "Failed to bind \"" << symbol << "\" to an unsupported term.";
			return false;
		}
		return true;
	}
	
	template<typename Term>
	bool handleITE(const FormulaT& ifterm, const Term& thenterm, const Term& elseterm, Term& result, TheoryError& errors) {
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
	
	template<typename Term>
	bool functionCall(const Identifier& identifier, const std::vector<Term>& arguments, Term& result, TheoryError& errors) {
		std::vector<FormulaT> args;
		auto it = ops.find(identifier);
		if (it == ops.end()) {
			errors.next() << "Invalid operator \"" << identifier << "\".";
			return false;
		}
		OperatorType op = it->second;
		if (!convertArguments(op, arguments, args, errors)) return false;
	
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
		/*if (boost::iequals(identifier.symbol, "distinct")) {
			if (convertArguments(identifier, arguments, args, errors)) {
				result = FormulaT(carl::FormulaType::IFF, args);
				return true;
			}
		} else if (boost::iequals(identifier.symbol, "ite")) {
			if (convertArguments(identifier, arguments, args, errors)) {
				result = FormulaT(carl::FormulaType::IFF, args);
				return true;
			}
		}*/
		return false;
	}
};
	
}
}
