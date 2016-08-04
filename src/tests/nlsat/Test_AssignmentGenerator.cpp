#include <boost/test/unit_test.hpp>

#include <iostream>

#include "../../lib/datastructures/AssignmentGenerator.h"

using namespace smtrat;

BOOST_AUTO_TEST_SUITE(Test_AssignmentGenerator);

BOOST_AUTO_TEST_CASE(Test_Foo)
{
	carl::Variable x = carl::freshRealVariable("x");
	carl::Variable y = carl::freshRealVariable("y");
	ConstraintT c1(x*x-Rational(1), carl::Relation::GEQ);
	ConstraintT c2(x*x-Rational(5)+y*y, carl::Relation::GEQ);
	ConstraintT c3(x*x-Rational(1), carl::Relation::LESS);
	
	AssignmentGenerator ag;
	ag.pushConstraint(c1);
	ag.pushConstraint(c2);
	ag.pushAssignment(y, Rational(1));

	BOOST_CHECK(ag.getAssignment(x));
	BOOST_CHECK(ag.getAssignment() == carl::RealAlgebraicNumber<Rational>(-3));
	
	ag.pushConstraint(c3);
	BOOST_CHECK(!ag.getAssignment(x));
	BOOST_CHECK(ag.getConflictingCore().size() == 2);
}

BOOST_AUTO_TEST_SUITE_END();
