#pragma once

#include "../Common.h"
#include "ParserState.h"
#include "Visitors.h"

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
	
	template<typename Operator, typename Term>
	static bool convertArguments(const Operator& op, const std::vector<Term>& arguments, std::vector<FormulaT>& result, TheoryError& errors) {
		result.clear();
		for (std::size_t i = 0; i < arguments.size(); i++) {
			if (boost::get<FormulaT>(&arguments[i]) == nullptr) {
				errors.next() << "Operator \"" << op << "\" expects arguments to be formulas, but argument " << (i+1) << " is not.";
				return false;
			}
			result.push_back(boost::get<FormulaT>(arguments[i]));
		}
		return true;
	}
	
	ParserState* state;
	std::map<std::string, OperatorType> ops;
	CoreTheory(ParserState* state): state(state) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		sm.interpretedSort("Bool", carl::VariableType::VT_BOOL);
		
		ops.emplace("not", OperatorType(carl::FormulaType::NOT));
		ops.emplace("=>", OperatorType(carl::FormulaType::IMPLIES));
		ops.emplace("and", OperatorType(carl::FormulaType::AND));
		ops.emplace("or", OperatorType(carl::FormulaType::OR));
		ops.emplace("xor", OperatorType(carl::FormulaType::XOR));
	}
	
	void addGlobalFormulas(FormulasT& formulas) {
	}
	bool newVariable(const std::string& name, const carl::Sort& sort) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		if (!sm.isInterpreted(sort)) return false;
		if (sm.interpretedType(sort) != carl::VariableType::VT_BOOL) return false;
		assert(state->isSymbolFree(name));
		state->var_bool[name] = carl::freshVariable(name, carl::VariableType::VT_BOOL);
		return true;
	}
	
	struct BindVisitor: public virtual visitors::BindVisitor {
		void operator()(const FormulaT& f) {
			state->bind_bool.emplace(symbol, f);
		}
	};
	
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
