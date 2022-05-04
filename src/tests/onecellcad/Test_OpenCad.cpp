#define BOOST_TEST_MODULE test_opencellcad

#include <boost/test/unit_test.hpp>

#include <carl/core/MultivariatePolynomial.h>
#include <carl/core/Variable.h>
#include <carl/ran/RealAlgebraicPoint.h>

#include <smtrat-mcsat/explanations/onecellcad/OpenCAD.h>

/**
  * References:
  * [1] Christopher W. Brown. 2013. Constructing a single open cell in a
  * cylindrical algebraic decomposition. In Proceedings of the 38th
  * International Symposium on Symbolic and Algebraic Computation (ISSAC '13).
  * ACM
  */

namespace {
  using std::cout;
  using std::endl;
  using std::optional;

  using smtrat::Rational;
  using namespace smtrat::onecellcad;
  using carl::Variable;
  using MultiPoly = carl::MultivariatePolynomial<Rational>;
	using RAN = carl::RealAlgebraicNumber<Rational>;
	using RANPoint = RealAlgebraicPoint<Rational>;

struct VariableFixture {
  Variable x = carl::freshRealVariable("x");
  Variable y = carl::freshRealVariable("y");
  Variable z = carl::freshRealVariable("z");
};

BOOST_FIXTURE_TEST_CASE(polylevel, VariableFixture) {
  BOOST_TEST_MESSAGE("Test polyLevel");

  std::vector<Variable> variableOrder {x,y,z};
  BOOST_CHECK(levelOf(MultiPoly(1),variableOrder) == 0);
  BOOST_CHECK(levelOf(MultiPoly(x)*Rational(0),variableOrder) == 0);
  BOOST_CHECK(levelOf(MultiPoly(x*y)*Rational(0),variableOrder) == 0);
  BOOST_CHECK(levelOf(MultiPoly(x),variableOrder) == 1);
  BOOST_CHECK(levelOf(MultiPoly(y),variableOrder) == 2);
  BOOST_CHECK(levelOf(MultiPoly(x*y),variableOrder) == 2);
  BOOST_CHECK(levelOf(MultiPoly(z),variableOrder) == 3);
  BOOST_CHECK(levelOf(MultiPoly(x*z),variableOrder) == 3);
  BOOST_CHECK(levelOf(MultiPoly(x*y*z),variableOrder) == 3);
}

BOOST_FIXTURE_TEST_CASE(cell2d, VariableFixture) {
  BOOST_TEST_MESSAGE("Test 2D example from [1]");
  MultiPoly p = MultiPoly(x*x) + MultiPoly(y*y) - Rational(1) ;
  MultiPoly q = MultiPoly(y*y)*Rational(2) - MultiPoly(x*x) * (MultiPoly(x)*Rational(2) + Rational(3)) ;
  MultiPoly r = MultiPoly(y) + MultiPoly(x)*Rational(0.5) - Rational(0.5) ;

  std::vector<MultiPoly> polys {p,q,r};
  RANPoint alpha { RAN(Rational(-1)/3), RAN(Rational(1)/3) };
  std::vector<Variable> variableOrder {x,y};

  optional<OpenCADCell> c = createOpenCADCell(polys, alpha, variableOrder);

  BOOST_CHECK(c);
}



} // namespace
