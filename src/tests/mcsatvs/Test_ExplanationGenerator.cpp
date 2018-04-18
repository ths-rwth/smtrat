#include <boost/test/included/unit_test.hpp> // TODO this is an ugly workaround
//#include <boost/test/unit_test.hpp>


#include <lib/datastructures/mcsat/vs/ExplanationGenerator.h>
#include <lib/logging.h>

using namespace smtrat;
using namespace mcsat::vs::helper;

BOOST_AUTO_TEST_SUITE(Test_ExplanationGenerator);

// TODO write tests
BOOST_AUTO_TEST_CASE(Test_generateZeros_eliminationVariableNotContained) {
	carl::Variable x = carl::freshRealVariable("x");
	carl::Variable y = carl::freshRealVariable("y");

	ConstraintT c1(Poly(x)+Rational(1), carl::Relation::LEQ);
	bool result = generateZeros(c1, y, [&](const SqrtEx&& sqrtExpression, const ConstraintsT&& sideConditions) {
    	BOOST_CHECK(false);
    });
	BOOST_CHECK(result);
}
BOOST_AUTO_TEST_CASE(Test_generateZeros_degreeToHigh) {
	carl::Variable x = carl::freshRealVariable("x");
	carl::Variable y = carl::freshRealVariable("y");

	ConstraintT c1(Poly(y)*y*y+Rational(1), carl::Relation::LEQ);
	bool result = generateZeros(c1, y, [&](const SqrtEx&& sqrtExpression, const ConstraintsT&& sideConditions) {
    	BOOST_CHECK(false);
    });
	BOOST_CHECK(result == false);

	int zeros = 0;
	ConstraintT c2(Poly(y)*y*x, carl::Relation::LEQ);
	result = generateZeros(c2, y, [&](const SqrtEx&& sqrtExpression, const ConstraintsT&& sideConditions) {
    	zeros++;
    });
	BOOST_CHECK(result == true);
	BOOST_CHECK(zeros > 0);
}
BOOST_AUTO_TEST_CASE(Test_generateZeros_deg1) {
	carl::Variable x = carl::freshRealVariable("x");
	carl::Variable y = carl::freshRealVariable("y");

	ConstraintT c1(0*Poly(y), carl::Relation::LESS);
	bool result = generateZeros(c1, y, [&](const SqrtEx&& sqrtExpression, const ConstraintsT&& sideConditions) {
    	BOOST_CHECK(false);
    });
	BOOST_CHECK(result);

	ConstraintT c2(Poly(y)*x+Rational(1), carl::Relation::EQ);
	result = generateZeros(c2, y, [&](const SqrtEx&& sqrtExpression, const ConstraintsT&& sideConditions) {
    	BOOST_CHECK(sqrtExpression==SqrtEx(Poly(-1), ZERO_POLYNOMIAL, Poly(x), ZERO_POLYNOMIAL));
		BOOST_CHECK(sideConditions.size() == 1);
		// TODO check that side condition is x != 0
    });
	BOOST_CHECK(result);
}

BOOST_AUTO_TEST_SUITE_END();
