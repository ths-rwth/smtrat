#define BOOST_TEST_MODULE test_onecellcad

#include <experimental/optional>

#include <boost/test/unit_test.hpp>

#include <carl/core/MultivariatePolynomial.h>
#include <carl/core/Variable.h>
#include <carl/formula/model/ran/RealAlgebraicPoint.h>

#include "../lib/Common.h"
#include "../../lib/datastructures/mcsat/onecellcad/OneCellCAD.h"

/**
  * References:
  * [1] Christopher W. Brown and Marek Košta. 2015. Constructing a single cell
  * in cylindrical algebraic decomposition. J. Symb. Comput. 70, C (September
  * 2015), 14-48. DOI=http://dx.doi.org/10.1016/j.jsc.2014.09.024
  */

namespace {
  using std::cout;
  using std::endl;
  using std::experimental::optional;
  using std::experimental::nullopt;

  using smtrat::Rational;
  using namespace smtrat::onecellcad;
  using carl::Variable;
  using MultiPoly = carl::MultivariatePolynomial<Rational>;
	using RAN = carl::RealAlgebraicNumber<Rational>;
	using RANPoint = carl::RealAlgebraicPoint<Rational>;

struct VariableFixture {
  Variable x = carl::freshRealVariable("x");
  Variable y = carl::freshRealVariable("y");
  Variable z = carl::freshRealVariable("z");
  std::vector<Variable> variableOrder {x,y,z};
};

BOOST_FIXTURE_TEST_CASE(polylevel, VariableFixture) {
  BOOST_TEST_MESSAGE("Test polyLevel");

  BOOST_CHECK(levelOf(variableOrder, MultiPoly(1)) == nullopt);
  BOOST_CHECK(levelOf(variableOrder, MultiPoly(x) * Rational(0)) == nullopt);
  BOOST_CHECK(levelOf(variableOrder, MultiPoly(x * y) * Rational(0)) == nullopt);
  BOOST_CHECK(*levelOf(variableOrder, MultiPoly(x)) == 0);
  BOOST_CHECK(*levelOf(variableOrder, MultiPoly(y)) == 1);
  BOOST_CHECK(*levelOf(variableOrder, MultiPoly(x * y)) == 1);
  BOOST_CHECK(*levelOf(variableOrder, MultiPoly(z)) == 2);
  BOOST_CHECK(*levelOf(variableOrder, MultiPoly(x * z)) == 2);
  BOOST_CHECK(*levelOf(variableOrder, MultiPoly(x * y * z)) == 2);
}

BOOST_FIXTURE_TEST_CASE(cell2d, VariableFixture) {
  BOOST_TEST_MESSAGE("Test 2D example from [1]");
  MultiPoly p = MultiPoly(x*x) + MultiPoly(y*y) - Rational(1) ;
  MultiPoly q = MultiPoly(y*y)*Rational(2) - MultiPoly(x*x) * (MultiPoly(x)*Rational(2) + Rational(3)) ;
  MultiPoly r = MultiPoly(y) + MultiPoly(x)*Rational(0.5) - Rational(0.5) ;
  std::vector<MultiPoly> polys {p,q,r};

  RANPoint alpha { RAN(Rational(-1)/3), RAN(Rational(1)/3) };

  optional<CADCell> c = pointEnclosingCADCell(variableOrder, alpha, polys);

  BOOST_CHECK(c);
}

} // namespace
