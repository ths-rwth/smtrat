#include "PolynomialParser.h"

#ifdef __VS
#pragma warning(push, 0)
#include <boost/fusion/include/std_pair.hpp>
#include <boost/spirit/include/phoenix_bind.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_object.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#pragma warning(pop)
#else
#include <boost/fusion/include/std_pair.hpp>
#include <boost/spirit/include/phoenix_bind.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_object.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#endif

#include "FormulaParser.h"

namespace smtrat {
namespace parser {

	PolynomialParser::PolynomialParser(ParserState* _state, FormulaParser* formulaPtr, UninterpretedParser* uninterpreted):
		PolynomialParser::base_type(polynomial, "polynomial"),
		state(_state),
		fun_argument(formulaPtr, uninterpreted, this)
	{
		polynomial_op = op_theory >> +polynomial;
		polynomial_op.name("polynomial operation");
		polynomial_ite = qi::lit("ite") >> (*formulaPtr >> polynomial >> polynomial)[qi::_val = px::bind(&PolynomialParser::mkIteInExpr, px::ref(*this), qi::_1, qi::_2, qi::_3)];
		polynomial_ite.name("polynomial if-then-else");
		polynomial_fun = (state->funmap_theory >> *fun_argument)[qi::_val = px::bind(&ParserState::applyTheoryFunction, px::ref(state), qi::_1, qi::_2)];
		polynomial_fun.name("theory function");
		polynomial_uf = (state->funmap_uftheory >> *fun_argument)[qi::_val = px::bind(&ParserState::applyUninterpretedTheoryFunction, px::ref(state), qi::_1, qi::_2)];
		polynomial_uf.name("uninterpreted theory function");
		polynomial =
				(state->bind_theory[qi::_val = qi::_1] >> boundary)
			|	(state->var_theory[qi::_val = px::bind(&PolynomialParser::var2Poly, px::ref(*this), qi::_1)] >> boundary)
			|	decimal[qi::_val = px::bind(&PolynomialParser::rationalToPoly, px::ref(*this), qi::_1)]
			|	integral[qi::_val = px::bind(&PolynomialParser::rationalToPoly, px::ref(*this), qi::_1)]
			|	("(" >> (
					polynomial_ite[qi::_val = qi::_1]
				|	polynomial_op[qi::_val = px::bind(&PolynomialParser::createPoly, px::ref(*this), qi::_1)]
				|	polynomial_fun[qi::_val = qi::_1]
				|	polynomial_uf[qi::_val = qi::_1]
			) >> ")")
		;
	}
	
	Poly PolynomialParser::mkIteInExpr(const FormulaT& _condition, Poly& _then, Poly& _else) {
		if (_then == _else) return _then;
		if (_condition == FormulaT(carl::FormulaType::FALSE)) return _else;
		if (_condition == FormulaT(carl::FormulaType::TRUE)) return _then;

		carl::Variable auxVar = (state->mLogic == Logic::QF_LIA || state->mLogic == Logic::QF_NIA) ? carl::freshIntegerVariable() : carl::freshRealVariable();

		state->mTheoryItes[auxVar] = std::make_tuple(_condition, _then, _else);
		return carl::makePolynomial<Poly>(auxVar);
	}
}
}
