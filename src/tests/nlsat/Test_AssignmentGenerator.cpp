#include <boost/test/unit_test.hpp>

#include <iostream>

#include "../../lib/datastructures/mcsat/nlsat/AssignmentGenerator.h"
#include "../../lib/datastructures/mcsat/nlsat/ExplanationGenerator.h"
#include "../../lib/datastructures/mcsat/nlsat/LemmaBuilder.h"

using namespace smtrat;
using namespace smtrat::nlsat;

BOOST_AUTO_TEST_SUITE(Test_AssignmentGenerator);

BOOST_AUTO_TEST_CASE(Test_NLSATPaper_Ex6)
{
	carl::Variable x = carl::freshRealVariable("x");
	carl::Variable y = carl::freshRealVariable("y");
	carl::Variable z = carl::freshRealVariable("z");
	
	Poly p = Poly(x*x) + y*y + z*z - Rational(1);
	ConstraintT c(p, carl::Relation::LESS);
	
	AssignmentGenerator ag;
	FormulaT fx(ConstraintT(Poly(x) - Rational(Rational(3)/Rational(4)), carl::Relation::EQ));
	ag.pushAssignment(x, Rational(3)/Rational(4), fx);
	FormulaT fy(ConstraintT(Poly(y) + Rational(Rational(3)/Rational(4)), carl::Relation::EQ));
	ag.pushAssignment(y, -Rational(3)/Rational(4), fy);
	ag.pushConstraint(FormulaT(c));
	BOOST_CHECK(!ag.hasAssignment(z));
	
	ExplanationGenerator eg(ag.getConflictingCore(), {z,y,x}, ag.getModel());
	
	std::vector<std::pair<carl::Variable,FormulaT>> assignment;
	assignment.emplace_back(x, fx);
	assignment.emplace_back(y, fy);
	LemmaBuilder lb(assignment, FormulaT(c).negated(), eg);
	lb.generateLemmas([this](const FormulaT& f){ std::cout << "-> " << f << std::endl; }, LemmaStrategy::ORIGINAL);
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
	ag.pushConstraint(FormulaT(c1));
	BOOST_CHECK(ag.hasAssignment(x));
	std::cout << ag.getAssignment() << std::endl; 
	BOOST_CHECK(ag.getAssignment() == Rational(-2));
	// Lift-Level -> x = -1
	FormulaT fx(ConstraintT(Poly(x) + Rational(1), carl::Relation::EQ));
	ag.pushAssignment(x, Rational(-1), fx);
	
	// Select c3, Decide c3
	ag.pushConstraint(FormulaT(c3));
	// R-Propagate !c4
	ag.pushConstraint(FormulaT(c4));
	
	BOOST_CHECK(!ag.hasAssignment(y));
	BOOST_CHECK(ag.getConflictingCore().size() == 2);
	
	ExplanationGenerator eg(ag.getConflictingCore(), {y,x}, ag.getModel());
	std::vector<std::pair<carl::Variable,FormulaT>> assignment;
	assignment.emplace_back(x, fx);

	LemmaBuilder lb(assignment, FormulaT(c4).negated(), eg);
	lb.generateLemmas([this](const FormulaT& f){ std::cout << "-> " << f << std::endl; }, LemmaStrategy::ORIGINAL);
}

BOOST_AUTO_TEST_SUITE_END();
