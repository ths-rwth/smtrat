#include <boost/test/unit_test.hpp>

#include <smtrat-mcsat/smtrat-mcsat.h>
#include <smtrat-mcsat/explanations/fm/Explanation.h>

using namespace smtrat;

BOOST_AUTO_TEST_SUITE(Test_Explanation_FM);

BOOST_AUTO_TEST_CASE(Test_One)
{
	
	carl::Variable a = carl::fresh_real_variable("a");
	carl::Variable b = carl::fresh_real_variable("b");
	
	// Original constraints
	FormulaT c1(Poly(b), carl::Relation::EQ);
	FormulaT c2(Poly(a)*b-Rational(1), carl::Relation::EQ);
	
	mcsat::Bookkeeping bk;
	bk.pushConstraint(c1);
	bk.pushConstraint(c2);
	mcsat::fm::Explanation<mcsat::fm::DefaultSettings> expl;
	
	{
		bk.pushAssignment(a, Rational(-1), FormulaT(VariableAssignmentT(a, Rational(-1))));
		auto ref = FormulaT(carl::FormulaType::OR, {
			c1.negated(),
			c2.negated(),
			FormulaT(ConstraintT(Poly(a), carl::Relation::GEQ))
		});
		auto res = expl(bk, b, {c1,c2});
		assert(res);
		std::cout << *res << std::endl;
		std::cout << "Should be " << ref << std::endl;
		BOOST_CHECK(boost::get<FormulaT>(&*res) != nullptr);
		BOOST_CHECK(ref == boost::get<FormulaT>(*res));
		bk.popAssignment(a);
	}
	{
		bk.pushAssignment(a, Rational(1), FormulaT(VariableAssignmentT(a, Rational(1))));
		auto ref = FormulaT(carl::FormulaType::OR, {
			c1.negated(),
			c2.negated(),
			FormulaT(ConstraintT(Poly(a), carl::Relation::LEQ))
		});
		std::cout << "Should be " << ref << std::endl;
		auto res = expl(bk, b, {c1,c2});
		assert(res);
		std::cout << *res << std::endl;
		BOOST_CHECK(boost::get<FormulaT>(&*res) != nullptr);
		BOOST_CHECK(ref == boost::get<FormulaT>(*res));
		bk.popAssignment(a);
	}
}

BOOST_AUTO_TEST_CASE(Test_Two)
{
	
	carl::Variable x = carl::fresh_real_variable("x");
	carl::Variable y = carl::fresh_real_variable("y");
	
	// Original constraints
	FormulaT c1(Poly(y), carl::Relation::GREATER);
	FormulaT c2(Poly(x) + Poly(y), carl::Relation::LESS);
	
	mcsat::Bookkeeping bk;
	bk.pushConstraint(c1);
	bk.pushConstraint(c2);
	mcsat::fm::Explanation<mcsat::fm::DefaultSettings> expl;
	
	{
		bk.pushAssignment(x, Rational(0), FormulaT(VariableAssignmentT(x, Rational(0))));
		auto res = expl(bk, y, {c1,c2});
		assert(res);
		std::cout << *res << std::endl;
	}
}

BOOST_AUTO_TEST_SUITE_END();
