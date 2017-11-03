#define BOOST_TEST_MODULE test_opencellcad
#include <boost/test/included/unit_test.hpp>

#include "../../lib/datastructures/onecellcad/OpenCAD.h"
/* #include <carl/core/UnivariatePolynomial.h> */
#include <carl/core/MultivariatePolynomial.h>
#include <carl/core/Variable.h>
/* #include <carl/formula/model/ran/RealAlgebraicPoint.h> */
/* #include <carl/formula/model/ran/RealAlgebraicNumber.h> */

#include "../lib/Common.h"

namespace {
  using std::cout;
  using std::endl;

  using smtrat::Rational;
  using carl::Variable;
  using MultiPoly = carl::MultivariatePolynomial<Rational>;

struct VariableFixture {
  Variable x = carl::freshRealVariable("x");
  Variable y = carl::freshRealVariable("y");
  Variable z = carl::freshRealVariable("z");
  std::vector<Variable> variableOrder {x,y,z};
};

BOOST_FIXTURE_TEST_CASE(simplest_test, VariableFixture) {
  BOOST_TEST_MESSAGE("Test");
  cout << x*y*z << endl;
  carl::MultivariatePolynomial<Rational> p(x*y);
  cout << p << endl;
  BOOST_TEST(1);
}

BOOST_FIXTURE_TEST_CASE(tmp, VariableFixture) {
  BOOST_TEST_MESSAGE("Test");
  carl::MultivariatePolynomial<Rational> p(x*y);
  cout << p << endl;
  BOOST_TEST(1);
}



} // namespace
