#include <boost/test/unit_test.hpp>

#include <iostream>

#include "../../lib/datastructures/AssignmentGenerator.h"
#include "../../lib/datastructures/ExplanationGenerator.h"

using namespace smtrat;

BOOST_AUTO_TEST_SUITE(Test_AssignmentGenerator);
(or (<= x (NR -1 R)) (>= x (NR 1 R)) (>= y root(_z^2+x^2+(-1), 1, _z)) (<= (+ (* (- 1) (* z z)) (* (- 1) (* y y)) (* (- 1) (* x x)) 1) 0))
BOOST_AUTO_TEST_CASE(Test_NLSATPaper_Ex6)
{
	carl::Variable x = carl::freshRealVariable("x");
	carl::Variable y = carl::freshRealVariable("y");
	carl::Variable z = carl::freshRealVariable("z");
	
	Poly p = Poly(x*x) + y*y + z*z - Rational(1);
	ConstraintT c(p, carl::Relation::LESS);
	
	AssignmentGenerator ag;
	ag.pushAssignment(x, Rational(3)/Rational(4));
	ag.pushAssignment(y, -Rational(3)/Rational(4));
	ag.pushConstraint(c);
	BOOST_CHECK(!ag.hasAssignment(z));
	
	ExplanationGenerator eg(ag.getConflictingCore(), {z,y,x}, ag.getModel());
	FormulaT res = eg.generateExplanation(c);
	std::cout << res << std::endl;
}

BOOST_AUTO_TEST_CASE(Test_NLSATPaper)
{
	// Implements the example from the nlsat paper.
	carl::Variable x = carl::freshRealVariable("x");
	carl::Variable y = carl::freshRealVariable("y");
	ConstraintT c1(Poly(x)+Rational(1), carl::Relation::LEQ);
	ConstraintT c2(Poly(x)-Rational(1), carl::Relation::GEQ);
	ConstraintT c3(Poly(x)+y, carl::Relation::GREATER);
	ConstraintT c4(Poly(x)-y, carl::Relation::GREATER);
	ConstraintT c4Inv(c4.lhs(), carl::invertRelation(c4.relation()));
	
	AssignmentGenerator ag;
	// Select c1, Decide c1
	ag.pushConstraint(c1);
	BOOST_CHECK(ag.hasAssignment(x));
	BOOST_CHECK(ag.getAssignment() == carl::RealAlgebraicNumber<Rational>(-2));
	// Lift-Level -> x = -1
	ag.pushAssignment(x, Rational(-1));
	
	// Select c3, Decide c3
	ag.pushConstraint(c3);
	// R-Propagate !c4
	ag.pushConstraint(c4);
	
	BOOST_CHECK(!ag.hasAssignment(y));
	BOOST_CHECK(ag.getConflictingCore().size() == 2);
	
	ExplanationGenerator eg(ag.getConflictingCore(), {y,x}, ag.getModel());
	FormulaT res = eg.generateExplanation(c4);
	std::cout << res << std::endl;
}

BOOST_AUTO_TEST_SUITE_END();
