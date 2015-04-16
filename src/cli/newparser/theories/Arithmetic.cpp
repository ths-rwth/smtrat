#include "Arithmetic.h"
#include "ParserState.h"

namespace smtrat {
namespace parser {
	void ArithmeticTheory::addSimpleSorts(qi::symbols<char, carl::Sort>& sorts) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		sorts.add("Int", sm.getInterpreted(carl::VariableType::VT_INT));
		sorts.add("Real", sm.getInterpreted(carl::VariableType::VT_REAL));
	}

	bool ArithmeticTheory::convertTerm(const types::TermType& term, Poly& result) {
		if (boost::get<Poly>(&term) != nullptr) {
			result = boost::get<Poly>(term);
			return true;
		} else if (boost::get<Rational>(&term) != nullptr) {
			result = Poly(boost::get<Rational>(term));
			return true;
		} else if (boost::get<carl::Variable>(&term) != nullptr) {
			switch (boost::get<carl::Variable>(term).getType()) {
				case carl::VariableType::VT_REAL:
				case carl::VariableType::VT_INT:
					result = Poly(boost::get<carl::Variable>(term));
					return true;
				default:
					return false;
			}
		} else {
			return false;
		}
	}

	bool ArithmeticTheory::convertArguments(const OperatorType& op, const std::vector<types::TermType>& arguments, std::vector<Poly>& result, TheoryError& errors) {
		result.clear();
		for (std::size_t i = 0; i < arguments.size(); i++) {
			Poly res;
			if (!convertTerm(arguments[i], res)) {
				errors.next() << "Operator \"" << op << "\" expects arguments to be formulas, but argument " << (i+1) << " is not: \"" << arguments[i] << "\".";
				return false;
			}
			result.push_back(res);
		}
		return true;
	}

	ArithmeticTheory::ArithmeticTheory(ParserState* state): AbstractTheory(state) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		sm.addInterpretedSort("Int", carl::VariableType::VT_INT);
		sm.addInterpretedSort("Real", carl::VariableType::VT_REAL);
		
		ops.emplace("+", OperatorType(Poly::ConstructorOperation::ADD));
		ops.emplace("-", OperatorType(Poly::ConstructorOperation::SUB));
		ops.emplace("*", OperatorType(Poly::ConstructorOperation::MUL));
		ops.emplace("/", OperatorType(Poly::ConstructorOperation::DIV));
		ops.emplace("<", OperatorType(carl::Relation::LESS));
		ops.emplace("<=", OperatorType(carl::Relation::LEQ));
		ops.emplace("=", OperatorType(carl::Relation::EQ));
		ops.emplace("!=", OperatorType(carl::Relation::NEQ));
		ops.emplace(">=", OperatorType(carl::Relation::GEQ));
		ops.emplace(">", OperatorType(carl::Relation::GREATER));
	}

	bool ArithmeticTheory::declareVariable(const std::string& name, const carl::Sort& sort) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		switch (sm.getType(sort)) {
			case carl::VariableType::VT_INT:
			case carl::VariableType::VT_REAL:
				assert(state->isSymbolFree(name));
				state->variables[name] = carl::freshVariable(name, sm.getType(sort));
				return true;
			default:
				return false;
		}
	}

	bool ArithmeticTheory::handleITE(const FormulaT& ifterm, const types::TermType& thenterm, const types::TermType& elseterm, types::TermType& result, TheoryError& errors) {
		Poly thenpoly;
		Poly elsepoly;
		if (!convertTerm(thenterm, thenpoly)) {
			errors.next() << "Failed to construct ITE, the then-term \"" << thenterm << "\" is unsupported.";
			return false;
		}
		if (!convertTerm(elseterm, elsepoly)) {
			errors.next() << "Failed to construct ITE, the else-term \"" << elseterm << "\" is unsupported.";
			return false;
		}
		carl::Variable auxVar = carl::freshRealVariable();
		mITEs[auxVar] = std::make_tuple(ifterm, thenpoly, elsepoly);
		result = carl::makePolynomial<Poly>(auxVar);
		return true;
	}

	FormulaT ArithmeticTheory::makeConstraint(const Poly& lhs, const Poly& rhs, carl::Relation rel) {
		Poly p = lhs - rhs;
		std::set<carl::Variable> pVars = p.gatherVariables();
		std::vector<carl::Variable> vars;
		while (!pVars.empty()) {
			auto it = mITEs.find(*pVars.begin());
			pVars.erase(pVars.begin());
			if (it != mITEs.end()) {
				std::get<1>(it->second).gatherVariables(pVars);
				std::get<2>(it->second).gatherVariables(pVars);
				vars.push_back(it->first);
			}
		}
		std::size_t n = vars.size();
		if (n == 0) {
			// There are no ITEs.
			ConstraintT cons = ConstraintT(p, rel);
			return FormulaT(cons);
		} else if (n < 4) {
			// There are only a few ITEs, hence we expand them here directly to 2^n cases.
			// 2^n Polynomials with values substituted.
			std::vector<Poly> polys({p});
			// 2^n Formulas collecting the conditions.
			std::vector<FormulasT> conds(1 << n);
			unsigned repeat = 1 << (n-1);
			for (auto v: vars) {
				auto t = mITEs[v];
				std::vector<Poly> ptmp;
				for (auto& p: polys) {
					// Substitute both possibilities for this ITE.
					ptmp.push_back(p.substitute(v, std::get<1>(t)));
					ptmp.push_back(p.substitute(v, std::get<2>(t)));
				}
				std::swap(polys, ptmp);
				// Add the conditions at the appropriate positions.
				FormulaT f[2]= { std::get<0>(t), FormulaT(carl::FormulaType::NOT, std::get<0>(t)) };
				for (size_t i = 0; i < (size_t)(1 << n); i++) {
					conds[i].insert(f[0]);
					if ((i+1) % repeat == 0) std::swap(f[0], f[1]);
				}
				repeat /= 2;
			}
			// Now combine everything: (and (=> (and conditions) constraint) ...)
			FormulasT subs;
			for (unsigned i = 0; i < polys.size(); i++) {
				subs.insert(FormulaT(carl::FormulaType::IMPLIES, FormulaT(carl::FormulaType::AND, conds[i]), FormulaT(polys[i], rel)));
			}
			auto res = FormulaT(carl::FormulaType::AND, subs);
			return res;
		} else {
			// There are many ITEs, we keep the auxiliary variables.
			for (const auto& v: vars) {
				auto t = mITEs[v];
				FormulaT consThen = FormulaT(std::move(carl::makePolynomial<Poly>(v) - std::get<1>(t)), carl::Relation::EQ);
				FormulaT consElse = FormulaT(std::move(carl::makePolynomial<Poly>(v) - std::get<2>(t)), carl::Relation::EQ);

				state->mGlobalFormulas.emplace(FormulaT(carl::FormulaType::IMPLIES,std::get<0>(t), consThen));
				state->mGlobalFormulas.emplace(FormulaT(carl::FormulaType::IMPLIES,FormulaT(carl::FormulaType::NOT,std::get<0>(t)), consElse));
			}
			return FormulaT(p, rel);
		}
	}

	bool ArithmeticTheory::functionCall(const Identifier& identifier, const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors) {
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
				result = makeConstraint(args[0], args[1], boost::get<carl::Relation>(op));
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
}
}
