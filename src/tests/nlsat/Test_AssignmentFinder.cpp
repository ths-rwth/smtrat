#include <boost/test/unit_test.hpp>

#include <lib/datastructures/mcsat/nlsat/AssignmentFinder.h>
#include <lib/datastructures/mcsat/nlsat/NLSAT.h>
#include <lib/logging.h>

using namespace smtrat;

BOOST_AUTO_TEST_SUITE(Test_AssignmentFinder);

/**
 * Tests Example 3 from the NLSAT-Paper
 */
BOOST_AUTO_TEST_CASE(Test_NLSATPaper_Ex3)
{
	
	carl::Variable x = carl::freshRealVariable("x");
	carl::Variable y = carl::freshRealVariable("y");
	
	// Original constraints
	FormulaT c1(Poly(x)+Rational(1), carl::Relation::LEQ);
	FormulaT c2(Poly(x)-Rational(1), carl::Relation::GEQ);
	FormulaT c3(Poly(x)+y, carl::Relation::GREATER);
	FormulaT c4(Poly(x)-y, carl::Relation::GREATER);
	// Learnt from first conflict
	FormulaT c5(Poly(x), carl::Relation::LESS);
	
	// Explanation for first conflict
	FormulaT ex1(carl::FormulaType::OR, { c3.negated(), c4.negated(), c5.negated() });
	// Explanation for second conflict
	FormulaT ex2(carl::FormulaType::OR, { c1.negated(), c5 });
	
	nlsat::NLSAT nlsat;
	
	// Decide x+1<=0
	SMTRAT_LOG_INFO("smtrat.test.nlsat", "Decide " << c1);
	nlsat.pushConstraint(c1);
	
	// T-Decide
	SMTRAT_LOG_INFO("smtrat.test.nlsat", "T-Decide " << x << " = -2");
	{
		auto res = nlsat.findAssignment(x);
		BOOST_CHECK(carl::variant_is_type<ModelValue>(res));
		auto value = boost::get<ModelValue>(res);
		BOOST_CHECK(value == Rational(-2));
	}
	FormulaT fx(Poly(x) + Rational(2), carl::Relation::EQ);
	nlsat.pushAssignment(x, Rational(-2), fx);
	
	// Propagate x+y>0
	SMTRAT_LOG_INFO("smtrat.test.nlsat", "Propagate " << c3);
	nlsat.pushConstraint(c3);
	
	// Check whether x-y>0 is feasible, propagate x-y<=0
	SMTRAT_LOG_INFO("smtrat.test.nlsat", "T-Propagate " << c4.negated());
	{
		auto res = nlsat.isInfeasible(y, c4);
		BOOST_CHECK(bool(res));
		auto explanation = nlsat.explain(y, *res, c4.negated());
		BOOST_CHECK(ex1 == explanation);
	}
	nlsat.pushConstraint(c4.negated());
	
	// Backtrack assignment
	SMTRAT_LOG_INFO("smtrat.test.nlsat", "Backtrack " << x);
	nlsat.popAssignment(x);
	
	// Check whether x>0 is feasible, propagate x<=0
	SMTRAT_LOG_INFO("smtrat.test.nlsat", "T-Propagate " << c5);
	{
		auto res = nlsat.isInfeasible(x, c5.negated());
		BOOST_CHECK(bool(res));
		auto explanation = nlsat.explain(x, *res, c5);
		BOOST_CHECK(ex2 == explanation);
	}
}

BOOST_AUTO_TEST_SUITE_END();
