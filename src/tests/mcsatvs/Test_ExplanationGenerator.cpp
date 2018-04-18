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


BOOST_AUTO_TEST_SUITE_END();
