#include <boost/test/unit_test.hpp>

#include <iostream>

#include "../../lib/datastructures/model/Model.h"

using namespace smtrat;

BOOST_AUTO_TEST_SUITE(Test_Model);

BOOST_AUTO_TEST_CASE(Test_ModelValue)
{
	{
		ModelValue mv(true);
		BOOST_TEST((mv.isBool() && mv.asBool()), "ModelValue is true");
	}
	{
		ModelValue mv(false);
		BOOST_TEST((mv.isBool() && !mv.asBool()), "ModelValue is false");
	}
	{
		ModelValue mv(Rational(3));
		BOOST_TEST((mv.isRational() && mv.asRational() == Rational(3)), "ModelValue is 3");
	}
}

BOOST_AUTO_TEST_CASE(Test_ModelSubstitution)
{
	carl::Variable x = carl::freshRealVariable("x");
	carl::Variable y = carl::freshRealVariable("y");
	Poly p(Rational(2) * x*x);
	Model m;
	m.emplace(ModelVariable(x), Rational(3));
	m.emplace(ModelVariable(y), ModelSubstitution::create<ModelPolynomialSubstitution>(p));
	
	for (const auto& mv: m) {
		if (mv.second.isSubstitution()) {
			std::cout << mv.first << " -> " << mv.second.asSubstitution() << std::endl;
		} else {
			std::cout << mv.first << " -> " << mv.second << std::endl;
		}
	}
}

BOOST_AUTO_TEST_SUITE_END();
