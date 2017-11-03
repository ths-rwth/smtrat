#define BOOST_TEST_MODULE test_opencellcad
#include <boost/test/included/unit_test.hpp>

/* #include "../../lib/datastructures/onecellcad/OpenCAD.h" */
/* #include <carl/core/UnivariatePolynomial.h> */
/* #include <carl/core/MultivariatePolynomial.h> */
#include <carl/core/Variable.h>
/* #include <carl/formula/model/ran/RealAlgebraicPoint.h> */
/* #include <carl/formula/model/ran/RealAlgebraicNumber.h> */

#include "../lib/Common.h"

BOOST_AUTO_TEST_CASE(first_test)
{
  int i = 1;
  BOOST_TEST(i);
  BOOST_TEST(i != 2);
}

BOOST_AUTO_TEST_CASE(simplest_test) {
  carl::Variable x = carl::freshRealVariable("x");
  carl::Variable y = carl::freshRealVariable("y");
  /* carl::MultivariatePolynomial<Rational> p(x*y); */
  /* std::cout << p << std::endl; */
}

