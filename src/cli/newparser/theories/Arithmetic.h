#pragma once

#include "../Common.h"
#include "ParserState.h"

namespace smtrat {
namespace parser {

struct ArithmeticTheory {
	typedef mpl::vector<Rational> ConstTypes;
	typedef mpl::vector<carl::Variable, Rational, Poly> ExpressionTypes;
	typedef mpl::vector<carl::Variable, Rational, Poly> TermTypes;
	typedef carl::mpl_variant_of<TermTypes>::type TermType;
	typedef boost::variant<Poly::ConstructorOperation, carl::Relation> OperatorType;
	
	static void addSimpleSorts(qi::symbols<char, carl::Sort>& sorts) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		sorts.add("Int", sm.interpretedSort(carl::VariableType::VT_INT));
		sorts.add("Real", sm.interpretedSort(carl::VariableType::VT_REAL));
	}
	template<typename T>
	static void addConstants(qi::symbols<char, T>& constants) {
	}
	template<typename T>
	static void addOperators(qi::symbols<char, T>& operators) {
	}
	
	template<typename Operator, typename Term>
	static bool convertArguments(const Operator& op, const std::vector<Term>& arguments, std::vector<Poly>& result, TheoryError& errors) {
		result.clear();
		for (std::size_t i = 0; i < arguments.size(); i++) {
			if (boost::get<Poly>(&arguments[i]) != nullptr) {
				result.push_back(boost::get<Poly>(arguments[i]));
			} else if (boost::get<Rational>(&arguments[i]) != nullptr) {
				result.push_back(Poly(boost::get<Rational>(arguments[i])));
			} else if (boost::get<carl::Variable>(&arguments[i]) != nullptr) {
				result.push_back(Poly(boost::get<carl::Variable>(arguments[i])));
			} else {
				errors.next() << "Operator \"" << op << "\" expects arguments to be numbers or polynomials, but argument " << (i+1) << " is not: \"" << arguments[i] << "\".";
				return false;
			}
		}
		return true;
	}
	
	ParserState* state;
	std::map<std::string, OperatorType> ops;
	ArithmeticTheory(ParserState* state): state(state) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		sm.interpretedSort("Int", carl::VariableType::VT_INT);
		sm.interpretedSort("Real", carl::VariableType::VT_REAL);
		
		ops.emplace("+", OperatorType(Poly::ConstructorOperation::ADD));
		ops.emplace("-", OperatorType(Poly::ConstructorOperation::SUB));
		ops.emplace("*", OperatorType(Poly::ConstructorOperation::MUL));
		ops.emplace("/", OperatorType(Poly::ConstructorOperation::DIV));
		ops.emplace("<", OperatorType(carl::Relation::LESS));
		ops.emplace("<=", OperatorType(carl::Relation::LEQ));
		ops.emplace("=", OperatorType(carl::Relation::EQ));
		ops.emplace("<", OperatorType(carl::Relation::LESS));
		ops.emplace("<", OperatorType(carl::Relation::LESS));
		ops.emplace("<", OperatorType(carl::Relation::LESS));
	}
	
	void addGlobalFormulas(FormulasT& formulas) {
	}
	bool newVariable(const std::string& name, const carl::Sort& sort) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		if (!sm.isInterpreted(sort)) return false;
		if ((sm.interpretedType(sort) != carl::VariableType::VT_REAL) && (sm.interpretedType(sort) != carl::VariableType::VT_INT)) return false;
		assert(state->isSymbolFree(name));
		state->var_arithmetic[name] = carl::freshVariable(name, sm.interpretedType(sort));
		return true;
	}
	
	struct BindVisitor: public virtual visitors::BindVisitor {
		void operator()(const carl::Variable& v) {
			state->bind_arithmetic.emplace(symbol, Poly(v));
		}
		void operator()(const Rational& r) {
			std::cout << "Binding " << symbol << " to " << r << std::endl;
			state->bind_arithmetic.emplace(symbol, Poly(r));
		}
		void operator()(const Poly& p) {
			state->bind_arithmetic.emplace(symbol, p);
		}
	};

	template<typename Term>
	bool functionCall(const Identifier& identifier, const std::vector<Term>& arguments, Term& result, TheoryError& errors) {
		std::vector<Poly> args;
		auto it = ops.find(identifier.symbol);
		if (it == ops.end()) {
			errors.next() << "Invalid operator \"" << identifier << "\".";
			return false;
		}
		OperatorType op = it->second;
		if (!convertArguments(op, arguments, args, errors)) return false;
		
		if (boost::get<Poly::ConstructorOperation>(&op) != nullptr) {
			result = Poly(boost::get<Poly::ConstructorOperation>(op), args);
		} else if (boost::get<carl::Relation>(&op) != nullptr) {
			if (args.size() == 2) {
				result = FormulaT(ConstraintT(args[0] - args[1], boost::get<carl::Relation>(op)));
			} else {
				errors.next() << "Operator \"" << boost::get<carl::Relation>(op) << "\" expects exactly two operands.";
				return false;
			}
		} else {
			errors.next() << "Invalid operator \"" << op << "\".";
			return false;
		}
		return true;
	}
};
	
}
}
