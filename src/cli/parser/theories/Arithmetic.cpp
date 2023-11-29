#include "Arithmetic.h"
#include "ParserState.h"
#include <carl-arith/core/Variable.h>
#include <smtrat-common/types.h>

namespace smtrat {
namespace parser {
inline bool ArithmeticTheory::convertTerm(const types::TermType& term, Poly& result, bool allow_bool) {
	if (boost::get<Poly>(&term) != nullptr) {
		result = boost::get<Poly>(term);
		return true;
	} else if (boost::get<Rational>(&term) != nullptr) {
		result = Poly(boost::get<Rational>(term));
		return true;
	} else if (boost::get<carl::Variable>(&term) != nullptr) {
		switch (boost::get<carl::Variable>(term).type()) {
		case carl::VariableType::VT_REAL:
		case carl::VariableType::VT_INT:
			result = Poly(boost::get<carl::Variable>(term));
			return true;
		case carl::VariableType::VT_BOOL:
			if (allow_bool) {
				result = Poly(boost::get<carl::Variable>(term));
				return true;
			}
			return false;
		default:
			return false;
		}
	} else if (allow_bool && boost::get<FormulaT>(&term) != nullptr) {
		FormulaT formula = boost::get<FormulaT>(term);
		const auto& mappedFormulaIt = mappedFormulas.find(formula);

		if (mappedFormulaIt != mappedFormulas.end()) {
			carl::Variable var = mappedFormulaIt->second;
			result = Poly(var);
		} else {
			carl::Variable var = carl::fresh_boolean_variable();
			FormulaT subst = FormulaT(carl::FormulaType::IFF, FormulaT(var), formula);

			state->global_formulas.emplace_back(subst);
			mappedFormulas[formula] = var;

			result = Poly(var);
		}

		return true;
	} else {
		return false;
	}
}

inline bool ArithmeticTheory::convertArguments(const arithmetic::OperatorType& op, const std::vector<types::TermType>& arguments, std::vector<Poly>& result, TheoryError& errors) {
	SMTRAT_LOG_DEBUG("smtrat.parser", "Converting arguments: " << arguments << " for operator " << op);
	result.clear();
	for (std::size_t i = 0; i < arguments.size(); i++) {
		Poly res;
		if (!convertTerm(arguments[i], res, state->logic == carl::Logic::QF_PB)) {
			errors.next() << "Operator \"" << op << "\" expects arguments to be polynomials, but argument " << (i + 1) << " is not: \"" << arguments[i] << "\".";
			return false;
		}
		result.push_back(res);
	}
	return true;
}

namespace arithmetic {
inline FormulaT makeConstraint(ArithmeticTheory& at, const Poly& lhs, const Poly& rhs, carl::Relation rel) {
	Poly p = lhs - rhs;
	carl::carlVariables pVars;
	carl::variables(p, pVars);
	std::vector<carl::Variable> vars;
	while (!pVars.empty()) {
		auto it = at.mITEs.find(*pVars.begin());
		pVars.erase(*pVars.begin());
		if (it != at.mITEs.end()) {
			carl::variables(std::get<1>(it->second), pVars);
			carl::variables(std::get<2>(it->second), pVars);
			vars.push_back(it->first);
		}
	}
	std::size_t n = vars.size();
	if (n == 0) {
		// There are no ITEs.
		ConstraintT cons = ConstraintT(p, rel);
		return FormulaT(cons);
	} else if (n < 1) {
		// There are only a few ITEs, hence we expand them here directly to 2^n cases.
		// 2^n Polynomials with values substituted.
		std::vector<Poly> polys({p});
		// 2^n Formulas collecting the conditions.
		std::vector<FormulasT> conds(1 << n);
		unsigned repeat = 1 << (n - 1);
		for (auto v : vars) {
			auto t = at.mITEs[v];
			std::vector<Poly> ptmp;
			for (auto& p : polys) {
				// Substitute both possibilities for this ITE.
				ptmp.push_back(carl::substitute(p, v, std::get<1>(t)));
				ptmp.push_back(carl::substitute(p, v, std::get<2>(t)));
			}
			std::swap(polys, ptmp);
			// Add the conditions at the appropriate positions.
			FormulaT f[2] = {std::get<0>(t), FormulaT(carl::FormulaType::NOT, std::get<0>(t))};
			for (size_t i = 0; i < (size_t)(1 << n); i++) {
				conds[i].push_back(f[0]);
				if ((i + 1) % repeat == 0) std::swap(f[0], f[1]);
			}
			repeat /= 2;
		}
		// Now combine everything: (and (=> (and conditions) constraint) ...)
		FormulasT subs;
		for (unsigned i = 0; i < polys.size(); i++) {
			subs.push_back(FormulaT(carl::FormulaType::IMPLIES, {FormulaT(carl::FormulaType::AND, conds[i]), FormulaT(polys[i], rel)}));
		}
		auto res = FormulaT(carl::FormulaType::AND, subs);

		return res;
	} else {
		// There are many ITEs, we keep the auxiliary variables.
		for (const auto& v : vars) {
			auto t = at.mITEs[v];
			FormulaT consThen = FormulaT(std::move(Poly(v) - std::get<1>(t)), carl::Relation::EQ);
			FormulaT consElse = FormulaT(std::move(Poly(v) - std::get<2>(t)), carl::Relation::EQ);

			at.state->global_formulas.emplace_back(FormulaT(carl::FormulaType::ITE, {std::get<0>(t), consThen, consElse}));
			//				state->global_formulas.emplace(FormulaT(carl::FormulaType::IMPLIES,std::get<0>(t), consThen));
			//				state->global_formulas.emplace(FormulaT(carl::FormulaType::IMPLIES,FormulaT(carl::FormulaType::NOT,std::get<0>(t)), consElse));
		}
		return FormulaT(p, rel);
	}
}

inline bool isBooleanIdentity(const OperatorType& op, const std::vector<types::TermType>& arguments, TheoryError& errors) {
	if (boost::get<carl::Relation>(&op) == nullptr) return false;
	if (boost::get<carl::Relation>(op) != carl::Relation::EQ) return false;
	for (const auto& a : arguments) {
		if (boost::get<carl::Variable>(&a) != nullptr) {
			if (boost::get<carl::Variable>(a).type() != carl::VariableType::VT_BOOL) return false;
		} else if (boost::get<FormulaT>(&a) == nullptr) {
			return false;
		}
	}
	errors.next() << "Operator \"" << op << "\" only has boolean variables which is handled by the core theory.";
	return true;
}
} // namespace arithmetic
struct ToRealInstantiator : public FunctionInstantiator {
	bool operator()(const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors) const {
		if (arguments.size() != 1) {
			errors.next() << "to_real should have a single argument";
			return false;
		}
		result = arguments[0];
		return true;
	}
};

void ArithmeticTheory::addSimpleSorts(qi::symbols<char, carl::Sort>& sorts) {
	carl::SortManager& sm = carl::SortManager::getInstance();
	sorts.add("Int", sm.getInterpreted(carl::VariableType::VT_INT));
	sorts.add("Real", sm.getInterpreted(carl::VariableType::VT_REAL));
}

ArithmeticTheory::ArithmeticTheory(ParserState* state)
	: AbstractTheory(state) {
	carl::SortManager& sm = carl::SortManager::getInstance();
	sm.addInterpretedSort("Int", carl::VariableType::VT_INT);
	sm.addInterpretedSort("Real", carl::VariableType::VT_REAL);

	state->registerFunction("to_real", new ToRealInstantiator());

	ops.emplace("+", arithmetic::OperatorType(Poly::ConstructorOperation::ADD));
	ops.emplace("-", arithmetic::OperatorType(Poly::ConstructorOperation::SUB));
	ops.emplace("*", arithmetic::OperatorType(Poly::ConstructorOperation::MUL));
	ops.emplace("/", arithmetic::OperatorType(Poly::ConstructorOperation::DIV));
	ops.emplace("<", arithmetic::OperatorType(carl::Relation::LESS));
	ops.emplace("<=", arithmetic::OperatorType(carl::Relation::LEQ));
	ops.emplace("=", arithmetic::OperatorType(carl::Relation::EQ));
	ops.emplace("!=", arithmetic::OperatorType(carl::Relation::NEQ));
	ops.emplace("<>", arithmetic::OperatorType(carl::Relation::NEQ));
	ops.emplace(">=", arithmetic::OperatorType(carl::Relation::GEQ));
	ops.emplace(">", arithmetic::OperatorType(carl::Relation::GREATER));
}

bool ArithmeticTheory::declareVariable(const std::string& name, const carl::Sort& sort, types::VariableType& result, TheoryError& errors) {
	carl::SortManager& sm = carl::SortManager::getInstance();
	switch (sm.getType(sort)) {
	case carl::VariableType::VT_INT:
	case carl::VariableType::VT_REAL: {
		assert(state->isSymbolFree(name));
		carl::Variable var = carl::fresh_variable(name, sm.getType(sort));
		state->variables[name] = var;
		result = var;
		return true;
	}
	default:
		errors.next() << "The requested sort was neither \"Int\" nor \"Real\" but \"" << sort << "\".";
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
	if (thenpoly == elsepoly) {
		result = thenpoly;
		return true;
	}
	if (ifterm.type() == carl::FormulaType::CONSTRAINT) {
		if (ifterm.constraint().relation() == carl::Relation::EQ) {
			if (ifterm.constraint() == ConstraintT(thenpoly - elsepoly, carl::Relation::EQ)) {
				result = elsepoly;
				return true;
			}
		} else if (ifterm.constraint().relation() == carl::Relation::NEQ) {
			if (ifterm.constraint() == ConstraintT(thenpoly - elsepoly, carl::Relation::NEQ)) {
				result = thenpoly;
				return true;
			}
		}
	} else if (ifterm.type() == carl::FormulaType::NOT && ifterm.subformula().type() == carl::FormulaType::CONSTRAINT) {
		if (ifterm.subformula().constraint().relation() == carl::Relation::EQ) {
			if (ifterm.subformula().constraint() == ConstraintT(thenpoly - elsepoly, carl::Relation::EQ)) {
				result = thenpoly;
				return true;
			}
		} else if (ifterm.subformula().constraint().relation() == carl::Relation::NEQ) {
			if (ifterm.subformula().constraint() == ConstraintT(thenpoly - elsepoly, carl::Relation::NEQ)) {
				result = elsepoly;
				return true;
			}
		}
	}
	carl::Variable auxVar = /*thenpoly.integer_valued() && elsepoly.integer_valued() ? carl::fresh_integer_variable() :*/ carl::fresh_real_variable();
	state->artificialVariables.emplace_back(auxVar);
	mITEs[auxVar] = std::make_tuple(ifterm, thenpoly, elsepoly);
	result = Poly(auxVar);
	return true;
}
bool ArithmeticTheory::handleDistinct(const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors) {
	std::vector<Poly> args;
	conversion::VectorVariantConverter<Poly> c;
	if (!c(arguments, args, errors)) return false;
	result = expandDistinct(args, [](const Poly& a, const Poly& b) {
		return FormulaT(a - b, carl::Relation::NEQ);
	});
	return true;
}

bool ArithmeticTheory::instantiate(const types::VariableType& var, const types::TermType& replacement, types::TermType& result, TheoryError& errors) {
	carl::Variable v;
	conversion::VariantConverter<carl::Variable> c;
	if (!c(var, v)) {
		errors.next() << "The variable is not an arithmetic variable.";
		return false;
	}
	if ((v.type() != carl::VariableType::VT_INT) && (v.type() != carl::VariableType::VT_REAL)) {
		errors.next() << "Sort is neither \"Int\" nor \"Real\" but \"" << v.type() << "\".";
		return false;
	}
	Poly repl;
	if (!convertTerm(replacement, repl)) {
		errors.next() << "Could not convert argument \"" << replacement << "\" to an arithmetic expression.";
		return false;
	}
	Instantiator<carl::Variable, Poly> instantiator;
	return instantiator.instantiate(v, repl, result);
}

bool ArithmeticTheory::functionCall(const Identifier& identifier, const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors) {
	SMTRAT_LOG_DEBUG("smtrat.parser", "Function call " << identifier.symbol << " with arguments " << arguments);
	std::vector<Poly> args;
	if (identifier.symbol == "to_int") {
		if (arguments.size() != 1) {
			errors.next() << "to_int should have a single argument";
			return false;
		}
		conversion::VariantConverter<carl::Variable> c;
		carl::Variable arg;
		if (!c(arguments[0], arg)) {
			errors.next() << "to_int should be called with a variable";
			return false;
		}
		carl::Variable v = carl::fresh_variable(carl::VariableType::VT_INT);
		FormulaT lower(Poly(v) - arg, carl::Relation::LEQ);
		FormulaT greater(Poly(v) - arg - Rational(1), carl::Relation::GREATER);
		state->global_formulas.emplace_back(FormulaT(carl::FormulaType::AND, {lower, greater}));
		result = v;
		return true;
	}
	if (identifier.symbol == "mod") {
		if (arguments.size() != 2) {
			errors.next() << "mod should have exactly two arguments.";
			return false;
		}
		conversion::VariantConverter<Rational> ci;
		Rational modulus;
		if (!ci(arguments[1], modulus)) {
			errors.next() << "mod should be called with an integer as second argument.";
			return false;
		}
		conversion::VariantConverter<carl::Variable> cv;
		carl::Variable arg;
		Rational rarg;
		if (cv(arguments[0], arg)) {
			carl::Variable v = carl::fresh_variable(carl::VariableType::VT_INT);
			carl::Variable u = carl::fresh_variable(carl::VariableType::VT_INT);
			FormulaT relation(Poly(v) - arg + u * modulus, carl::Relation::EQ);
			FormulaT geq(Poly(v), carl::Relation::GEQ);
			FormulaT less(Poly(v) - modulus, carl::Relation::LESS);
			state->global_formulas.emplace_back(FormulaT(carl::FormulaType::AND, {relation, geq, less}));
			result = v;
			return true;
		} else if (ci(arguments[0], rarg)) {
			Integer lhs = carl::to_int<Integer>(rarg);
			Integer rhs = carl::to_int<Integer>(modulus);
			result = carl::mod(lhs, rhs);
			return true;
		} else {
			errors.next() << "mod should be called with a variable as first argument.";
			return false;
		}
	}
	if (identifier.symbol == "root") {
		if (arguments.size() != 3) {
			errors.next() << "root should have exactly three arguments.";
			return false;
		}
		Poly p;
		if (!convertTerm(arguments[0], p)) {
			errors.next() << "root should be called with a polynomial as first argument.";
			return false;
		}
		conversion::VariantConverter<Rational> ci;
		Rational k;
		if (!ci(arguments[1], k)) {
			errors.next() << "root should be called with an integer as second argument.";
			return false;
		}
		conversion::VariantConverter<carl::Variable> cv;
		carl::Variable var;
		if (!cv(arguments[2], var)) {
			errors.next() << "root should be called with a variable as third argument.";
			return false;
		}
		result = carl::MultivariateRoot<Poly>(p, carl::to_int<std::size_t>(carl::get_num(k)), var);
		return true;
	}
	auto it = ops.find(identifier.symbol);
	if (it == ops.end()) {
		errors.next() << "Invalid operator \"" << identifier << "\".";
		return false;
	}
	arithmetic::OperatorType op = it->second;
	if (boost::get<carl::Relation>(&op) != nullptr && arguments.size() == 3 && boost::get<FormulaT>(&arguments[0]) != nullptr && boost::get<carl::Variable>(&arguments[1]) != nullptr && boost::get<carl::MultivariateRoot<Poly>>(&arguments[2]) != nullptr) {
		bool negated = boost::get<FormulaT>(arguments[0]).type() == carl::FormulaType::TRUE;
		carl::Variable var = boost::get<carl::Variable>(arguments[1]);
		carl::MultivariateRoot<Poly> root = boost::get<carl::MultivariateRoot<Poly>>(arguments[2]);
		carl::Relation rel = boost::get<carl::Relation>(op);
		result = FormulaT(carl::VariableComparison<Poly>(var, root, rel, negated));
		return true;
	}
	if (arithmetic::isBooleanIdentity(op, arguments, errors)) return false;
	if (!convertArguments(op, arguments, args, errors)) return false;

	if (boost::get<Poly::ConstructorOperation>(&op) != nullptr) {
		auto o = boost::get<Poly::ConstructorOperation>(op);
		if (o == Poly::ConstructorOperation::DIV) {
			if (args.size() != 2) {
				errors.next() << "Division needs to have two operands.";
				return false;
			}
			if (carl::is_zero(args[1]) || !args[1].is_number()) {
				/*
				Ackermanize division:
				For each p/q:
				(q != 0 => div_pq*q = p) == (q = 0 || div_pq*q = p)
				For each p/q, p'/q'
				((p = p' and q = q') => div_pq = div_pq') == (p != p' || q != q' || div_pq = div_pq')
				*/

				std::stringstream name;
				name << "div_" << mNewDivisions.size() + mKnownDivisions.size();
				auto div_var_new = carl::fresh_variable(name.str(), carl::VariableType::VT_REAL);
				auto p_new = Poly(args[0]);
				auto q_new = Poly(args[1]);

				//(q != 0 => div_pq*q = p) == (q = 0 || div_pq*q = p)
				// const FormulaT lhs_s = FormulaT(ConstraintT(q_new, carl::Relation::NEQ));
				// const FormulaT rhs_s = FormulaT(ConstraintT(Poly(div_var_new)*q_new - p_new, carl::Relation::EQ));
				// const FormulaT div_formula(carl::FormulaType::IMPLIES, lhs_s, rhs_s);
				const FormulaT den_is0 = FormulaT(ConstraintT(q_new, carl::Relation::EQ));
				const FormulaT div_formula(carl::FormulaType::OR, den_is0, FormulaT(ConstraintT(Poly(div_var_new) * q_new - p_new, carl::Relation::EQ)));
				SMTRAT_LOG_DEBUG("smtrat.parser", "Adding division formula: " << div_formula);
				state->global_formulas.emplace_back(div_formula);

				for (const auto& [div_var_old, div_pair_old] : mKnownDivisions) {
					// ((p = p' and q = q') => div_pq = div_pq') == (p != p' || q != q' || div_pq = div_pq')
					const auto& [p_old, q_old] = div_pair_old;
					// const FormulaT lhs = FormulaT(carl::FormulaType::AND, FormulaT(ConstraintT(p_new - p_old, carl::Relation::EQ)), FormulaT(ConstraintT(q_new - q_old, carl::Relation::EQ)));
					// const FormulaT rhs = FormulaT(ConstraintT(Poly(div_var_new) - Poly(div_var_old), carl::Relation::EQ));
					// const FormulaT div_formula_pairwise(carl::FormulaType::IMPLIES, lhs, rhs);

					const FormulaT p_new_neq_p_old = FormulaT(ConstraintT(p_new - p_old, carl::Relation::NEQ));
					const FormulaT q_new_neq_q_old = FormulaT(ConstraintT(q_new - q_old, carl::Relation::NEQ));
					const FormulaT div_eq = FormulaT(ConstraintT(Poly(div_var_new) - Poly(div_var_old), carl::Relation::EQ));
					const FormulaT div_formula_pairwise(carl::FormulaType::OR, p_new_neq_p_old, q_new_neq_q_old, div_eq);

					SMTRAT_LOG_DEBUG("smtrat.parser", "Adding division pairwise formula: " << div_formula_pairwise);
					state->global_formulas.emplace_back(div_formula_pairwise);
				}
				mKnownDivisions[div_var_new] = std::make_pair(p_new, q_new);

				result = Poly(div_var_new);
				return true;
			}
			result = Poly(o, args);
			return true;
		} else {
			result = Poly(o, args);
		}
	} else if (boost::get<carl::Relation>(&op) != nullptr) {
		if (args.size() == 2) {
			result = arithmetic::makeConstraint(*this, args[0], args[1], boost::get<carl::Relation>(op));
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

bool ArithmeticTheory::declareQuantifiedTerm(const std::vector<std::pair<std::string, carl::Sort>>& vars, const carl::FormulaType& type, const types::TermType& term, types::TermType& result, smtrat::parser::TheoryError& errors) {
	SMTRAT_LOG_DEBUG("smtrat.parser", "Declaring quantified term " << term << " with quantification " << type << " and variables " << vars);
	std::vector<carl::Variable> variables;
	for (const auto& v : vars) {
		auto it = state->variables.find(v.first);
		if (it == state->variables.end()) {
			errors.next() << "Variable " << v.first << " not declared.";
			return false;
		}
		variables.push_back(boost::get<carl::Variable>(it->second));
	}
	result = FormulaT(type, std::move(variables), boost::get<FormulaT>(term));
	return true;
}
} // namespace parser
} // namespace smtrat
