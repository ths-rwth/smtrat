#include "FormulaParser.h"

#include <boost/fusion/include/std_pair.hpp>
#include <boost/phoenix.hpp>
#include <boost/spirit/include/phoenix_bind.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_object.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>

namespace smtrat {
namespace parser {

FormulaParser::FormulaParser(ParserState* _state):
	FormulaParser::base_type(formula, "formula"),
	state(_state),
	uninterpreted(_state, this),
	polynomial(_state, this, &uninterpreted),
	fun_argument(this, &uninterpreted, &polynomial)
{
	binding = symbol[qi::_a = qi::_1] > (
			polynomial[px::bind(&ParserState::addTheoryBinding, px::ref(state), qi::_a, qi::_1)]
		|	formula[px::bind(&ParserState::addBooleanBinding, px::ref(state), qi::_a, qi::_1)]
		|	uninterpreted[px::bind(&ParserState::addUninterpretedBinding, px::ref(state), qi::_a, qi::_1)]
	);
	binding.name("binding");
	bindlist = +(qi::lit("(") > binding > qi::lit(")"));
	bindlist.name("binding list");
	
	quantifiedVar = ("(" >> symbol >> -domain >> ")")[qi::_val = px::bind(&ParserState::addQuantifiedVariable, px::ref(state), qi::_1, qi::_2)];
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
				((qi::lit("=") >> +fun_argument)[qi::_val = px::bind(&FormulaParser::mkEquality, px::ref(*this), qi::_1)])
			|	((op_bool >> formula_list)[qi::_val = px::bind(&FormulaParser::mkFormula, px::ref(*this), qi::_1, qi::_2)])
			|	(relation >> polynomial >> polynomial)[qi::_val = px::bind(&FormulaParser::mkConstraint, px::ref(*this), qi::_2, qi::_3, qi::_1)]
			|	(qi::lit("as")[px::bind(&ParserState::errorMessage, px::ref(state), "\"as\" is not supported."), qi::_pass = false] > symbol > symbol)
			|	(qi::lit("distinct") >> +fun_argument)[qi::_val = px::bind(&FormulaParser::mkDistinct, px::ref(*this), qi::_1)]
			|	(qi::lit("not") > formula[qi::_val = px::construct<smtrat::FormulaT>(carl::FormulaType::NOT, qi::_1)])
			|	((qi::lit("implies") | "=>") > formula > formula)[qi::_val = px::construct<smtrat::FormulaT>(carl::FormulaType::IMPLIES, qi::_1, qi::_2)]
			|	(qi::lit("let")[px::bind(&ParserState::pushScope, px::ref(state))]
				> ("(" > bindlist > ")" > formula)[px::bind(&ParserState::popScope, px::ref(state)), qi::_val = qi::_1])
			|	(qi::lit("exists")[px::bind(&ParserState::pushScope, px::ref(state))] > "(" > *quantifiedVar > ")" > formula)[qi::_val = px::construct<smtrat::FormulaT>(carl::FormulaType::EXISTS, std::move(qi::_1), qi::_2), px::bind(&ParserState::popScope, px::ref(state))]
			|	(qi::lit("forall")[px::bind(&ParserState::pushScope, px::ref(state))] > "(" > *quantifiedVar > ")" > formula)[qi::_val = px::construct<smtrat::FormulaT>(carl::FormulaType::FORALL, std::move(qi::_1), qi::_2), px::bind(&ParserState::popScope, px::ref(state))]
			|	("ite" >> (formula >> formula >> formula)[qi::_val = px::construct<smtrat::FormulaT>(carl::FormulaType::ITE, qi::_1, qi::_2, qi::_3)])
			|	(("!" > formula > *attribute)[px::bind(&annotateFormula, qi::_1, qi::_2), qi::_val = qi::_1])
			|	((state->funmap_bool >> *fun_argument)[qi::_val = px::bind(&ParserState::applyBooleanFunction, px::ref(state), qi::_1, qi::_2)])
			|	((state->funmap_ufbool >> *fun_argument)[qi::_val = px::bind(&ParserState::applyUninterpretedBooleanFunction, px::ref(state), qi::_1, qi::_2)])
	;
	formula_op.name("formula operation");
}

FormulaT FormulaParser::mkFormula( carl::FormulaType type, FormulasT& _subformulas )
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
		FormulasT subs;
		for (unsigned i = 0; i < polys.size(); i++) {
			subs.insert(FormulaT(carl::FormulaType::IMPLIES, FormulaT(carl::FormulaType::AND, conds[i]), FormulaT(polys[i], rel)));
		}
		auto res = FormulaT(carl::FormulaType::AND, subs);
		return res;
	} else {
		// There are many ITEs, we keep the auxiliary variables.
		for (auto v: vars) {
			auto t = state->mTheoryItes[v];
			FormulaT consThen = FormulaT(std::move(carl::makePolynomial<Poly>(v) - std::get<1>(t)), carl::Relation::EQ);
			FormulaT consElse = FormulaT(std::move(carl::makePolynomial<Poly>(v) - std::get<2>(t)), carl::Relation::EQ);

			state->mTheoryIteBindings.emplace(FormulaT(carl::FormulaType::IMPLIES,std::get<0>(t), consThen));
			state->mTheoryIteBindings.emplace(FormulaT(carl::FormulaType::IMPLIES,FormulaT(carl::FormulaType::NOT,std::get<0>(t)), consElse));
		}
		return FormulaT(p, rel);
	}
}

class EqualityGenerator: public boost::static_visitor<FormulaT> {
private:
	bool negate;
	FormulaParser* parser;
public:
	EqualityGenerator(bool negate, FormulaParser* parser): negate(negate), parser(parser) {}
	FormulaT operator()(const FormulaT& lhs, const FormulaT& rhs) {
		if (negate) return FormulaT(carl::FormulaType::XOR, lhs, rhs);
		else return FormulaT(carl::FormulaType::IFF, lhs, rhs);
	}
	FormulaT operator()(const Poly& lhs, const Poly& rhs) {
		if (negate) return FormulaT(parser->mkConstraint(lhs, rhs, carl::Relation::NEQ));
		else return FormulaT(parser->mkConstraint(lhs, rhs, carl::Relation::EQ));
	}
	FormulaT operator()(const carl::UVariable& lhs, const carl::UVariable& rhs) {
		return FormulaT(lhs, rhs, negate);
	}
	FormulaT operator()(const carl::UVariable& lhs, const carl::UFInstance& rhs) {
		return FormulaT(lhs, rhs, negate);
	}
	FormulaT operator()(const carl::UFInstance& lhs, const carl::UVariable& rhs) {
		return FormulaT(lhs, rhs, negate);
	}
	FormulaT operator()(const carl::UFInstance& lhs, const carl::UFInstance& rhs) {
		return FormulaT(lhs, rhs, negate);
	}
	template<typename U, typename V>
	FormulaT operator()(const U& u, const V& v) {
		SMTRAT_LOG_ERROR("smtrat.parser", "Comparing two expressions that are not comparable: " << u << " == " << v);
		return FormulaT();
	}
};

FormulaT FormulaParser::mkEquality(const Arguments& args) {
	FormulasT subformulas;
	EqualityGenerator eg(false, this);
	for (std::size_t i = 0; i < args.size() - 1; i++) {
		subformulas.insert(boost::apply_visitor(eg, args[i], args[i+1]));
	}
	return FormulaT(carl::FormulaType::AND, subformulas);
}

FormulaT FormulaParser::mkDistinct(const Arguments& args) {
	FormulasT subformulas;
	EqualityGenerator eg(true, this);
	for (std::size_t i = 0; i < args.size() - 1; i++) {
		for (std::size_t j = i + 1; j < args.size(); j++) {
			subformulas.insert(boost::apply_visitor(eg, args[i], args[j]));
		}
	}
	return FormulaT(carl::FormulaType::AND, subformulas);
}

}
}
