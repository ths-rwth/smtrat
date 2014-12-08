#include "FormulaParser.h"

#include <boost/fusion/include/std_pair.hpp>
#include <boost/spirit/include/phoenix_bind.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_object.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>

namespace smtrat {
namespace parser {

FormulaParser::FormulaParser(ParserState* state):
	FormulaParser::base_type(formula, "formula"), 
	uninterpreted(state, this),
	polynomial(state, this, &uninterpreted),
	fun_argument(this, &uninterpreted, &polynomial)
{
	this->state = state;
	
	binding = symbol[qi::_a = qi::_1] > (
			polynomial[px::bind(&FormulaParser::addTheoryBinding, px::ref(*this), qi::_a, qi::_1)]
		|	formula[px::bind(&FormulaParser::addBooleanBinding, px::ref(*this), qi::_a, qi::_1)]
		|	uninterpreted[px::bind(&FormulaParser::addUninterpretedBinding, px::ref(*this), qi::_a, qi::_1)]
	);
	binding.name("binding");
	bindlist = +(qi::lit("(") > binding > qi::lit(")"));
	bindlist.name("binding list");
	
	quantifiedVar = ("(" >> symbol >> -domain >> ")")[qi::_val = px::bind(&FormulaParser::addQuantifiedVariable, px::ref(*this), qi::_1, qi::_2)];
	quantifiedVar.name("quantified variable");
	
	formula = 
			(state->bind_bool >> boundary)[qi::_val = qi::_1]
		|	(state->var_bool >> boundary)[qi::_val = px::construct<smtrat::FormulaT>(qi::_1)]
		|	qi::lit("true")[qi::_val = px::construct<smtrat::FormulaT>(carl::FormulaType::TRUE)]
		|	qi::lit("false")[qi::_val = px::construct<smtrat::FormulaT>(carl::FormulaType::FALSE)]
		|	("(" >> formula_op >> ")")[qi::_val = qi::_1]
	;
	formula.name("formula");
	
	formula_list = +formula;
	formula_list.name("formula list");
	formula_op =
				((op_bool >> formula_list)[qi::_val = px::bind(&FormulaParser::mkFormula, px::ref(*this), qi::_1, qi::_2)])
			|	(relation >> polynomial >> polynomial)[qi::_val = px::bind(&FormulaParser::mkConstraint, px::ref(*this), qi::_2, qi::_3, qi::_1)]
			|	((qi::lit("=") >> uninterpreted >> uninterpreted)[qi::_val = px::construct<smtrat::FormulaT>(qi::_1, qi::_2, false)])
			|	(qi::lit("as")[px::bind(&ParserState::errorMessage, px::ref(state), "\"as\" is not supported."), qi::_pass = false] > symbol > symbol)
			|	(qi::lit("distinct")[px::bind(&ParserState::errorMessage, px::ref(state), "\"distinct\" is not supported."),qi::_pass = false] > +formula)
			|	(qi::lit("not") > formula[qi::_val = px::construct<smtrat::FormulaT>(carl::FormulaType::NOT, qi::_1)])
			|	((qi::lit("implies") | "=>") > formula > formula)[qi::_val = px::construct<smtrat::FormulaT>(carl::FormulaType::IMPLIES, qi::_1, qi::_2)]
			|	(qi::lit("let")[px::bind(&ParserState::pushScope, px::ref(state))]
				> ("(" > bindlist > ")" > formula)[px::bind(&ParserState::popScope, px::ref(state)), qi::_val = qi::_1])
			|	(qi::lit("exists")[px::bind(&ParserState::pushScope, px::ref(state))] > "(" > *quantifiedVar > ")" > formula)[qi::_val = px::construct<smtrat::FormulaT>(carl::FormulaType::EXISTS, std::move(qi::_1), qi::_2), px::bind(&ParserState::popScope, px::ref(state))]
			|	(qi::lit("forall")[px::bind(&ParserState::pushScope, px::ref(state))] > "(" > *quantifiedVar > ")" > formula)[qi::_val = px::construct<smtrat::FormulaT>(carl::FormulaType::FORALL, std::move(qi::_1), qi::_2), px::bind(&ParserState::popScope, px::ref(state))]
			|	("ite" >> (formula >> formula >> formula)[qi::_val = px::construct<smtrat::FormulaT>(carl::FormulaType::ITE, qi::_1, qi::_2, qi::_3)])
			|	(("!" > formula > *attribute)[px::bind(&annotateFormula, qi::_1, qi::_2), qi::_val = qi::_1])
			|	((state->funmap_bool >> *fun_argument)[qi::_val = px::bind(&FormulaParser::applyBooleanFunction, px::ref(*this), qi::_1, qi::_2)])
			|	((state->funmap_ufbool >> *fun_argument)[qi::_val = px::bind(&FormulaParser::applyUninterpretedBooleanFunction, px::ref(*this), qi::_1, qi::_2)])
	;
	formula_op.name("formula operation");
}

FormulaT FormulaParser::mkFormula( carl::FormulaType type, std::set<FormulaT>& _subformulas )
{
	assert(type == carl::FormulaType::AND || type == carl::FormulaType::OR || type == carl::FormulaType::XOR || type == carl::FormulaType::IFF);
	return FormulaT(type, _subformulas);
}

FormulaT FormulaParser::mkConstraint(const Poly& lhs, const Poly& rhs, carl::Relation rel) {
	Poly p = lhs - rhs;
	std::set<carl::Variable> pVars = p.gatherVariables();
	std::vector<carl::Variable> vars;
	while (!pVars.empty()) {
		auto it = state->mTheoryItes.find(*pVars.begin());
		pVars.erase(pVars.begin());
		if (it != state->mTheoryItes.end()) {
			std::get<1>(it->second).gatherVariables(pVars);
			std::get<2>(it->second).gatherVariables(pVars);
			vars.push_back(it->first);
		}
	}
	std::size_t n = vars.size();
	if (n == 0) {
		// There are no ITEs.
		const ConstraintT* cons = carl::newConstraint<smtrat::Poly>(p, rel);
		return FormulaT(cons);
	} else if (n < 4) {
		// There are only a few ITEs, hence we expand them here directly to 2^n cases.
		// 2^n Polynomials with values substituted.
		std::vector<Poly> polys({p});
		// 2^n Formulas collecting the conditions.
		std::vector<std::set<FormulaT>> conds(1 << n);
		unsigned repeat = 1 << (n-1);
		for (auto v: vars) {
			auto t = state->mTheoryItes[v];
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
		std::set<FormulaT> subs;
		for (unsigned i = 0; i < polys.size(); i++) {
			subs.insert(FormulaT(carl::FormulaType::IMPLIES, FormulaT(carl::FormulaType::AND, conds[i]), FormulaT(polys[i], rel)));
		}
		auto res = FormulaT(carl::FormulaType::AND, subs);
		return res;
	} else {
		// There are many ITEs, we keep the auxiliary variables.
		for (auto v: vars) {
			auto t = state->mTheoryItes[v];
			FormulaT consThen = FormulaT(Poly(v) - std::get<1>(t), carl::Relation::EQ);
			FormulaT consElse = FormulaT(Poly(v) - std::get<2>(t), carl::Relation::EQ);

			state->mTheoryIteBindings.emplace(FormulaT(carl::FormulaType::IMPLIES,std::get<0>(t), consThen));
			state->mTheoryIteBindings.emplace(FormulaT(carl::FormulaType::IMPLIES,FormulaT(carl::FormulaType::NOT,std::get<0>(t)), consElse));
		}
		return FormulaT(p, rel);
	}
}

carl::Variable FormulaParser::addQuantifiedVariable(const std::string& _name, const boost::optional<carl::VariableType>& type) {
	std::string name = _name;
	for (unsigned id = 1; !state->isSymbolFree(name, false); id++) {
		name = _name + "_q" + std::to_string(id);
	}
	if (type.is_initialized()) {
		switch (TypeOfTerm::get(type.get())) {
			case ExpressionType::BOOLEAN: {
				carl::Variable v = carl::newBooleanVariable(name);
				state->var_bool.sym.remove(_name);
				state->var_bool.sym.add(_name, v);
				return v;
			}
			case ExpressionType::THEORY: {
				carl::Variable v = carl::newArithmeticVariable(name, type.get());
				state->var_theory.sym.remove(_name);
				state->var_theory.sym.add(_name, v);
				return v;
			}
			default: { // case ExpressionType::UNINTERPRETED
				state->handler->error() << "Tried to quantify over an uninterpreted type.";
				assert(false);
				return carl::Variable::NO_VARIABLE;
			}
		}
	} else if (state->var_bool.sym.find(_name) != nullptr) {
		carl::Variable v = carl::newBooleanVariable(name);
		state->var_bool.sym.remove(_name);
		state->var_bool.sym.add(_name, v);
		return v;
	} else if (state->var_theory.sym.find(_name) != nullptr) {
		carl::Variable v = carl::newArithmeticVariable(name, state->var_theory.sym.at(_name).getType());
		state->var_theory.sym.remove(_name);
		state->var_theory.sym.add(_name, v);
		return v;
	} else {
		state->handler->error() << "Tried to quantify <" << _name << "> but no type could be inferred.";
		return carl::Variable::NO_VARIABLE;
	}
}

void FormulaParser::addTheoryBinding(std::string& _varName, Poly& _polynomial) {
	assert(state->isSymbolFree(_varName));
	state->bind_theory.sym.add(_varName, _polynomial);
}

void FormulaParser::addBooleanBinding(std::string& _varName, const FormulaT& _formula) {
	assert(state->isSymbolFree(_varName));
	state->bind_bool.sym.add(_varName, _formula);
}

void FormulaParser::addUninterpretedBinding(std::string& _varName, const UninterpretedType& _uninterpreted) {
	assert(state->isSymbolFree(_varName));
	state->bind_uninterpreted.sym.add(_varName, _uninterpreted);
}

FormulaT FormulaParser::applyBooleanFunction(const BooleanFunction& f, const Arguments& args) {
	std::map<carl::Variable, FormulaT> boolAssignments;
	std::map<carl::Variable, Poly> theoryAssignments;
	if (!state->checkArguments(std::get<0>(f), std::get<1>(f), args, boolAssignments, theoryAssignments)) {
		return FormulaT();
	}
	return std::get<2>(f).substitute(boolAssignments, theoryAssignments);
}
FormulaT FormulaParser::applyUninterpretedBooleanFunction(const carl::UninterpretedFunction& f, const Arguments& args) {
	carl::Variable v = carl::newAuxiliaryBooleanVariable();
	state->mUninterpretedEqualities.insert(FormulaT(std::move(carl::UEquality(carl::UVariable(v), state->applyUninterpretedFunction(f, args), false))));
	return FormulaT(v);
}

}
}
