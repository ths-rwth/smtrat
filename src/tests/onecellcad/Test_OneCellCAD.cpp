#define BOOST_TEST_MODULE test_onecellcad

#include <optional>

#include <boost/test/unit_test.hpp>

#include <carl/poly/umvpoly/MultivariatePolynomial.h>
#include <carl/core/Variable.h>
#include <carl/ran/RealAlgebraicPoint.h>

#include <smtrat-mcsat/explanations/onecellcad/OneCellCAD.h>

/**
  * References:
  * [1] Christopher W. Brown and Marek Košta. 2015. Constructing a single cell
  * in cylindrical algebraic decomposition. J. Symb. Comput. 70, C (September
  * 2015), 14-48. DOI=http://dx.doi.org/10.1016/j.jsc.2014.09.024
  */

namespace {
  using std::cout;
  using std::endl;
  using std::optional;
  using std::nullopt;

  using smtrat::Rational;
  using namespace smtrat::mcsat::onecellcad;
  using carl::Variable;
  using Poly = carl::MultivariatePolynomial<Rational>;
	using RAN = carl::RealAlgebraicNumber<Rational>;
	using RANPoint = RealAlgebraicPoint<Rational>;

struct VariableFixture {
  Variable x = carl::freshRealVariable("x");
  Variable y = carl::freshRealVariable("y");
  Variable z = carl::freshRealVariable("z");
  std::vector<Variable> varOrder {x};
  std::vector<Variable> varOrder2 {x,y};
  std::vector<Variable> varOrder3 {x,y,z};
};

BOOST_FIXTURE_TEST_CASE(polylevel, VariableFixture) {
  BOOST_TEST_MESSAGE("Test polyLevel");

  BOOST_CHECK(levelOf(varOrder3, Poly(1)) == nullopt);
  BOOST_CHECK(levelOf(varOrder3, Poly(x) * Rational(0)) == nullopt);
  BOOST_CHECK(levelOf(varOrder3, Poly(x * y) * Rational(0)) == nullopt);
  BOOST_CHECK(*levelOf(varOrder3, Poly(x)) == 0);
  BOOST_CHECK(*levelOf(varOrder3, Poly(y)) == 1);
  BOOST_CHECK(*levelOf(varOrder3, Poly(x * y)) == 1);
  BOOST_CHECK(*levelOf(varOrder3, Poly(z)) == 2);
  BOOST_CHECK(*levelOf(varOrder3, Poly(x * z)) == 2);
  BOOST_CHECK(*levelOf(varOrder3, Poly(x * y * z)) == 2);
}

BOOST_FIXTURE_TEST_CASE(cell2d, VariableFixture) {
  BOOST_TEST_MESSAGE("Test 2D example from [1]");
  Poly p = Poly(x*x) + Poly(y*y) - Rational(1) ;
  Poly q = Poly(y*y)*Rational(2) - Poly(x*x) * (Poly(x)*Rational(2) + Rational(3)) ;
  Poly r = Poly(y) + Poly(x)*Rational(0.5) - Rational(0.5) ;
  std::vector<Poly> polys {p,q,r};

  RANPoint point { RAN(Rational(-1)/3), RAN(Rational(1)/3) };

  optional<CADCell> c = OneCellCAD(varOrder3,point).createCADCellAroundPoint(polys);

  BOOST_CHECK(c);
}

} // namespace
