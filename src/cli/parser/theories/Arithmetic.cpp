#include "Arithmetic.h"
#include "ParserState.h"

namespace smtrat {
namespace parser {
	struct ToRealInstantiator: public FunctionInstantiator {
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

	bool ArithmeticTheory::convertTerm(const types::TermType& term, Poly& result) {
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
		
		state->registerFunction("to_real", new ToRealInstantiator());
		
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

	bool ArithmeticTheory::declareVariable(const std::string& name, const carl::Sort& sort, types::VariableType& result, TheoryError& errors) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		switch (sm.getType(sort)) {
			case carl::VariableType::VT_INT:
			case carl::VariableType::VT_REAL: {
				assert(state->isSymbolFree(name));
				carl::Variable var = carl::freshVariable(name, sm.getType(sort));
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
                if( thenpoly == elsepoly )
                {
                    result = thenpoly;
                    return true;
                }
                if( ifterm.getType() == carl::FormulaType::CONSTRAINT )
                {
                    if( ifterm.constraint().relation() == carl::Relation::EQ )
                    {
                        if( ifterm.constraint() == ConstraintT( thenpoly-elsepoly, carl::Relation::EQ ) )
                        {
                            result = elsepoly;
                            return true;
                        }
                    }
                    else if( ifterm.constraint().relation() == carl::Relation::NEQ )
                    {
                        if( ifterm.constraint() == ConstraintT( thenpoly-elsepoly, carl::Relation::NEQ ) )
                        {
                            result = thenpoly;
                            return true;
                        }
                    }
                }
                else if( ifterm.getType() == carl::FormulaType::NOT && ifterm.subformula().getType() == carl::FormulaType::CONSTRAINT )
                {
                    if( ifterm.subformula().constraint().relation() == carl::Relation::EQ )
                    {
                        if( ifterm.subformula().constraint() == ConstraintT( thenpoly-elsepoly, carl::Relation::EQ ) )
                        {
                            result = thenpoly;
                            return true;
                        }
                    }
                    else if( ifterm.subformula().constraint().relation() == carl::Relation::NEQ )
                    {
                        if( ifterm.subformula().constraint() == ConstraintT( thenpoly-elsepoly, carl::Relation::NEQ ) )
                        {
                            result = elsepoly;
                            return true;
                        }
                    }   
                }
		carl::Variable auxVar = thenpoly.integerValued() && elsepoly.integerValued() ? carl::freshIntegerVariable() : carl::freshRealVariable();
		state->artificialVariables.emplace_back(auxVar);
		mITEs[auxVar] = std::make_tuple(ifterm, thenpoly, elsepoly);
		result = carl::makePolynomial<Poly>(auxVar);
		return true;
	}
	bool ArithmeticTheory::handleDistinct(const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors) {
		std::vector<Poly> args;
		conversion::VectorVariantConverter<Poly> c;
		if (!c(arguments, args, errors)) return false;
		result = expandDistinct(args, [](const Poly& a, const Poly& b){ 
			return FormulaT(a - b, carl::Relation::NEQ);
		});
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
		} else if (n < 1) {
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
					conds[i].push_back(f[0]);
					if ((i+1) % repeat == 0) std::swap(f[0], f[1]);
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
			for (const auto& v: vars) {
				auto t = mITEs[v];
				FormulaT consThen = FormulaT(std::move(carl::makePolynomial<Poly>(v) - std::get<1>(t)), carl::Relation::EQ);
				FormulaT consElse = FormulaT(std::move(carl::makePolynomial<Poly>(v) - std::get<2>(t)), carl::Relation::EQ);

                state->global_formulas.emplace_back(FormulaT(carl::FormulaType::ITE, {std::get<0>(t),consThen,consElse}));
//				state->global_formulas.emplace(FormulaT(carl::FormulaType::IMPLIES,std::get<0>(t), consThen));
//				state->global_formulas.emplace(FormulaT(carl::FormulaType::IMPLIES,FormulaT(carl::FormulaType::NOT,std::get<0>(t)), consElse));
			}
			return FormulaT(p, rel);
		}
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
		Instantiator<carl::Variable,Poly> instantiator;
		return instantiator.instantiate(v, repl, result);
	}

	bool ArithmeticTheory::functionCall(const Identifier& identifier, const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors) {
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
			carl::Variable v = carl::freshVariable(carl::VariableType::VT_INT);
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
				carl::Variable v = carl::freshVariable(carl::VariableType::VT_INT);
				carl::Variable u = carl::freshVariable(carl::VariableType::VT_INT);
				FormulaT relation(Poly(v) - arg + u * modulus, carl::Relation::EQ);
				FormulaT geq(Poly(v), carl::Relation::GEQ);
				FormulaT less(Poly(v) - modulus, carl::Relation::LESS);
				state->global_formulas.emplace_back(FormulaT(carl::FormulaType::AND, {relation, geq, less}));
				result = v;
				return true;
			} else if (ci(arguments[0], rarg)) {
				Integer lhs = carl::toInt<Integer>(rarg);
				Integer rhs = carl::toInt<Integer>(modulus);
				result = carl::mod(lhs, rhs);
				return true;
			} else {
				errors.next() << "mod should be called with a variable as first argument.";
				return false;
			}
		}
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
