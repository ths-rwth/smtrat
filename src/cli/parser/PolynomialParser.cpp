#include "PolynomialParser.h"

#include <boost/fusion/include/std_pair.hpp>
#include <boost/spirit/include/phoenix_bind.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_object.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>

#include "../../lib/Common.h"

#include "FormulaParser.h"

namespace smtrat {
namespace parser {

	PolynomialParser::PolynomialParser(ParserState* state, FormulaParser* formulaPtr, UninterpretedParser* uninterpreted):
		PolynomialParser::base_type(polynomial, "polynomial"),
		state(state),
		formulaPtr(formulaPtr),
		fun_argument(formulaPtr, uninterpreted, this)
	{
		polynomial_op = op_theory >> +polynomial;
		polynomial_op.name("polynomial operation");
		polynomial_ite = qi::lit("ite") >> (formula() >> polynomial >> polynomial)[qi::_val = px::bind(&PolynomialParser::mkIteInExpr, px::ref(*this), qi::_1, qi::_2, qi::_3)];
		polynomial_ite.name("polynomial if-then-else");
		polynomial_fun = (state->funmap_theory >> *fun_argument)[qi::_val = px::bind(&PolynomialParser::applyTheoryFunction, px::ref(*this), qi::_1, qi::_2)];
		polynomial_fun.name("theory function");
		polynomial_uf = (state->funmap_uftheory >> *fun_argument)[qi::_val = px::bind(&PolynomialParser::applyUninterpretedTheoryFunction, px::ref(*this), qi::_1, qi::_2)];
		polynomial_uf.name("uninterpreted theory function");
		polynomial =
				(state->bind_theory >> boundary)
			|	(state->var_theory >> boundary)
			|	decimal
			|	integral
			|	("(" >> (
					polynomial_ite
				|	polynomial_op
				|	polynomial_fun
				|	polynomial_uf
			) >> ")")
		;
	}
	
	Poly PolynomialParser::applyTheoryFunction(const TheoryFunction& f, const Arguments& args) {
		std::map<carl::Variable, FormulaT> boolAssignments;
		std::map<carl::Variable, Poly> theoryAssignments;
		if (!state->checkArguments(std::get<0>(f), std::get<1>(f), args, boolAssignments, theoryAssignments)) {
			return smtrat::Poly();
		}
		return std::get<2>(f).substitute(theoryAssignments);
	}

	Poly PolynomialParser::applyUninterpretedTheoryFunction(const carl::UninterpretedFunction& f, const Arguments& args) {
		assert(carl::SortManager::getInstance().isInterpreted(f.codomain()));

		carl::Variable v = carl::newAuxiliaryVariable(carl::SortManager::getInstance().interpretedType(f.codomain()));
		state->mUninterpretedEqualities.insert(FormulaT(std::move(carl::UEquality(carl::UVariable(v), state->applyUninterpretedFunction(f, args), false))));
		return Poly(v);
	}
	
	Poly PolynomialParser::mkIteInExpr(const FormulaT& _condition, Poly& _then, Poly& _else) {
		if (_then == _else) return _then;
		if (_condition == FormulaT(carl::FormulaType::FALSE)) return _else;
		if (_condition == FormulaT(carl::FormulaType::TRUE)) return _then;

		carl::Variable auxVar = (state->mLogic == Logic::QF_LIA || state->mLogic == Logic::QF_NIA) ? carl::newAuxiliaryIntVariable() : carl::newAuxiliaryRealVariable();

		state->mTheoryItes[auxVar] = std::make_tuple(_condition, _then, _else);
		return Poly(auxVar);
	}
}
}
