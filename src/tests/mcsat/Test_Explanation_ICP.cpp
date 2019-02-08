#include <boost/test/unit_test.hpp>


#include <smtrat-common/smtrat-common.h>
#include <smtrat-mcsat/explanations/icp/IntervalPropagation.h>

using namespace smtrat;

BOOST_AUTO_TEST_SUITE(Test_Explanation_ICP);

BOOST_AUTO_TEST_CASE(Test_Basic) {
	carl::Variable x = carl::freshRealVariable("x");
	carl::Variable y = carl::freshRealVariable("y");
	carl::Variable z = carl::freshRealVariable("z");

	Model model;
	model.emplace(x, Rational(4)/10);
	model.emplace(y, Rational(15)/100);

	ConstraintT c1(Poly(x)-Poly(z), carl::Relation::EQ);
	ConstraintT c2(Poly(x)*x-Poly(z), carl::Relation::EQ);
	ConstraintT c3(Poly(y)-Poly(x)*x, carl::Relation::LESS);
	ConstraintT c4(Poly(y)-Poly(1)/10, carl::Relation::GREATER);
	
	mcsat::icp::IntervalPropagation ip({x, y, z}, { FormulaT(c1), FormulaT(c2), FormulaT(c3), FormulaT(c4) }, model);
	auto res = ip.execute();
	if (res) {
		std::cout << *res << std::endl;
	}
}


BOOST_AUTO_TEST_SUITE_END();
