#include <boost/test/unit_test.hpp>
#include <boost/optional/optional_io.hpp>

#include <iostream>

#include "../../lib/modules/PBPPModule/CardinalityEncoder.h"

using namespace smtrat;

struct CardinalityFixture {
    CardinalityFixture() { }

    CardinalityEncoder encoder;
};

BOOST_FIXTURE_TEST_SUITE( s, CardinalityFixture )

BOOST_AUTO_TEST_SUITE( CardinalityEncoder )
BOOST_AUTO_TEST_SUITE( Equality );

BOOST_AUTO_TEST_CASE( CardinalityEncoder_Simple_EQ )
{
	carl::Variable x = carl::freshBooleanVariable("x");
	carl::Variable y = carl::freshBooleanVariable("y");
	
	ConstraintT constraint = ConstraintT(Poly(x) + Poly(y) + Rational(-1), carl::Relation::EQ);

	boost::optional<FormulaT> result = encoder.encode(constraint);

	if (!result) {
		BOOST_FAIL("result != {} expected, but got {}.");
	}

	FormulaT expected = FormulaT(carl::FormulaType::OR, FormulaT(carl::FormulaType::AND, FormulaT(x), !FormulaT(y)), FormulaT(carl::FormulaType::AND, !FormulaT(x), FormulaT(y)));

	BOOST_TEST(expected == *result, "expected " << expected << " but got " << result);
}

BOOST_AUTO_TEST_CASE( CardinalityEncoder_Simple_EQ_3_1 )
{
	carl::Variable x = carl::freshBooleanVariable("x");
	carl::Variable y = carl::freshBooleanVariable("y");
	carl::Variable z = carl::freshBooleanVariable("z");
	
	ConstraintT constraint = ConstraintT(Poly(x) + Poly(y) + Poly(z) + Rational(-1), carl::Relation::EQ);

	boost::optional<FormulaT> result = encoder.encode(constraint);

	if (!result) {
		BOOST_FAIL("result != {} expected, but got {}.");
	}

	FormulaT expected = FormulaT(carl::FormulaType::OR,
			FormulaT(carl::FormulaType::AND, !FormulaT(x), !FormulaT(y), FormulaT(z)),
			FormulaT(carl::FormulaType::AND, FormulaT(x), !FormulaT(y), !FormulaT(z)),
			FormulaT(carl::FormulaType::AND, !FormulaT(x), FormulaT(y), !FormulaT(z)));

	BOOST_TEST(expected == *result, "expected " << expected << " but got " << result);
}

BOOST_AUTO_TEST_CASE( CardinalityEncoder_Simple_EQ_3_2 )
{
	carl::Variable x = carl::freshBooleanVariable("x");
	carl::Variable y = carl::freshBooleanVariable("y");
	carl::Variable z = carl::freshBooleanVariable("z");
	
	ConstraintT constraint = ConstraintT(Poly(x) + Poly(y) + Poly(z) + Rational(-2), carl::Relation::EQ);

	boost::optional<FormulaT> result = encoder.encode(constraint);

	if (!result) {
		BOOST_FAIL("result != {} expected, but got {}.");
	}

	FormulaT expected = FormulaT(carl::FormulaType::OR,
			FormulaT(carl::FormulaType::AND, !FormulaT(x), FormulaT(y), FormulaT(z)),
			FormulaT(carl::FormulaType::AND, FormulaT(x), !FormulaT(y), FormulaT(z)),
			FormulaT(carl::FormulaType::AND, FormulaT(x), FormulaT(y), !FormulaT(z)));

	BOOST_TEST(expected == *result, "expected " << expected << " but got " << result);
}

BOOST_AUTO_TEST_CASE( CardinalityEncoder_Simple_EQ_3_2_Negative )
{
	carl::Variable x = carl::freshBooleanVariable("x");
	carl::Variable y = carl::freshBooleanVariable("y");
	carl::Variable z = carl::freshBooleanVariable("z");

	ConstraintT constraint = ConstraintT(-Poly(x) - Poly(y) - Poly(z) - Rational(-2), carl::Relation::EQ);

	boost::optional<FormulaT> result = encoder.encode(constraint);

	if (!result) {
		BOOST_FAIL("result != {} expected, but got {}.");
	}

	FormulaT expected = FormulaT(carl::FormulaType::OR,
			FormulaT(carl::FormulaType::AND, !FormulaT(x), FormulaT(y), FormulaT(z)),
			FormulaT(carl::FormulaType::AND, FormulaT(x), !FormulaT(y), FormulaT(z)),
			FormulaT(carl::FormulaType::AND, FormulaT(x), FormulaT(y), !FormulaT(z)));

	BOOST_TEST(expected == *result, "expected " << expected << " but got " << result);
}

BOOST_AUTO_TEST_CASE( CardinalityEncoder_Simple_EQ_FALSE )
{
	carl::Variable x = carl::freshBooleanVariable("x");
	carl::Variable y = carl::freshBooleanVariable("y");
	carl::Variable z = carl::freshBooleanVariable("z");
	
	ConstraintT constraint = ConstraintT(-Poly(x) - Poly(y) - Poly(z) - Rational(-4), carl::Relation::EQ);

	boost::optional<FormulaT> result = encoder.encode(constraint);

	if (!result) {
		BOOST_FAIL("result != {} expected, but got {}.");
	}

	FormulaT expected = FormulaT(carl::FormulaType::FALSE);

	BOOST_TEST(expected == *result, "expected " << expected << " but got " << result);
}

// END TEST SUITE EQ
BOOST_AUTO_TEST_SUITE_END();

BOOST_AUTO_TEST_CASE( CardinalityEncoder_Simple_LEQ_TRUE )
{
	carl::Variable x = carl::freshBooleanVariable("x");
	carl::Variable y = carl::freshBooleanVariable("y");
	carl::Variable z = carl::freshBooleanVariable("z");
	
	ConstraintT constraint = ConstraintT(-Poly(x) - Poly(y) - Poly(z) - Rational(-4), carl::Relation::EQ);

	boost::optional<FormulaT> result = encoder.encode(constraint);

	if (!result) {
		BOOST_FAIL("result != {} expected, but got {}.");
	}

	FormulaT expected = FormulaT(carl::FormulaType::AND, FormulaT(carl::FormulaType::OR, FormulaT(x), !FormulaT(y)), FormulaT(carl::FormulaType::OR, !FormulaT(x), FormulaT(y)));

	BOOST_TEST(expected == *result, "expected " << expected << " but got " << result);
}

BOOST_AUTO_TEST_CASE(CardinalityEncoder_Simple_LEQ)
{
	carl::Variable x = carl::freshBooleanVariable("x");
	carl::Variable y = carl::freshBooleanVariable("y");
	
	ConstraintT constraint = ConstraintT(Poly(x) + Poly(y) + Rational(-1), carl::Relation::LEQ);

	boost::optional<FormulaT> result = encoder.encode(constraint);

	if (!result) {
		BOOST_FAIL("result != {} expected, but got {}.");
	}

	FormulaT expected = FormulaT(carl::FormulaType::AND, FormulaT(carl::FormulaType::OR, FormulaT(x), FormulaT(y)), FormulaT(carl::FormulaType::OR, !FormulaT(x), !FormulaT(y)));

	BOOST_TEST(expected == *result, "expected " << expected << " but got " << result);
}


BOOST_AUTO_TEST_CASE(CardinalityEncoder_PositiveCoeff_AtMost)
{
	carl::Variable x1 = carl::freshBooleanVariable("x1");
	carl::Variable x2 = carl::freshBooleanVariable("x2");
	carl::Variable x3 = carl::freshBooleanVariable("x3");
	carl::Variable x4 = carl::freshBooleanVariable("x4");

	// x1 + x2 + x3 + x4 <= 2
	ConstraintT constraint = ConstraintT(Poly(x1) + Poly(x2) + Poly(x3) + Poly(x4) + Rational(-2), carl::Relation::LEQ);

	boost::optional<FormulaT> result = encoder.encode(constraint);

	if (!result) {
		BOOST_FAIL("result != {} expected, but got {}.");
	}

	FormulaT expected = FormulaT(carl::FormulaType::AND, FormulaT(carl::FormulaType::OR, FormulaT(x1), FormulaT(x2)), FormulaT(carl::FormulaType::OR, !FormulaT(x1), !FormulaT(x2)));

	BOOST_TEST(expected == *result, "expected " << expected << " but got " << result);
}

BOOST_AUTO_TEST_CASE(CardinalityEncoder_PositiveCoeff_AtMost_Strict)
{
	carl::Variable x1 = carl::freshBooleanVariable("x1");
	carl::Variable x2 = carl::freshBooleanVariable("x2");
	carl::Variable x3 = carl::freshBooleanVariable("x3");

	// x1 + x2 + x3 < 3
	ConstraintT constraint = ConstraintT(Poly(x1) + Poly(x2) + Poly(x3) + Rational(-3), carl::Relation::LESS);

	boost::optional<FormulaT> result = encoder.encode(constraint);

	if (!result) {
		BOOST_FAIL("result != {} expected, but got {}.");
	}

	FormulaT expected = FormulaT(carl::FormulaType::AND, FormulaT(carl::FormulaType::OR, FormulaT(x1), FormulaT(x2)), FormulaT(carl::FormulaType::OR, !FormulaT(x1), !FormulaT(x2)));

	BOOST_TEST(expected == *result, "expected " << expected << " but got " << result);
}

BOOST_AUTO_TEST_CASE(CardinalityEncoder_PositiveCoeff_AtMost_True)
{
	carl::Variable x1 = carl::freshBooleanVariable("x1");
	carl::Variable x2 = carl::freshBooleanVariable("x2");
	carl::Variable x3 = carl::freshBooleanVariable("x3");
	carl::Variable x4 = carl::freshBooleanVariable("x4");

	// x1 + x2 + x3 + x4 <= 10
	ConstraintT constraint = ConstraintT(Poly(x1) + Poly(x2) + Poly(x3) + Poly(x4) + Rational(-10), carl::Relation::LEQ);

	boost::optional<FormulaT> result = encoder.encode(constraint);

	if (!result) {
		BOOST_FAIL("result != {} expected, but got {}.");
	}

	FormulaT expected = FormulaT(carl::FormulaType::TRUE);

	BOOST_TEST(expected == *result, "expected " << expected << " but got " << result);
}

BOOST_AUTO_TEST_CASE(CardinalityEncoder_PositiveCoeff_AtMost_False)
{
	carl::Variable x1 = carl::freshBooleanVariable("x1");
	carl::Variable x2 = carl::freshBooleanVariable("x2");
	carl::Variable x3 = carl::freshBooleanVariable("x3");
	carl::Variable x4 = carl::freshBooleanVariable("x4");

	// x1 + x2 + x3 + x4 <= -1
	ConstraintT constraint = ConstraintT(Poly(x1) + Poly(x2) + Poly(x3) + Poly(x4) + Rational(1), carl::Relation::LEQ);

	boost::optional<FormulaT> result = encoder.encode(constraint);

	if (!result) {
		BOOST_FAIL("result != {} expected, but got {}.");
	}

	FormulaT expected = FormulaT(carl::FormulaType::TRUE);

	BOOST_TEST(expected == *result, "expected " << expected << " but got " << result);
}

BOOST_AUTO_TEST_CASE(CardinalityEncoder_Simple2)
{
	carl::Variable x = carl::freshBooleanVariable("y");
	carl::Variable y = carl::freshBooleanVariable("y");
	
	ConstraintT constraint = ConstraintT(Poly(x) + Poly(y) + Rational(-1), carl::Relation::LEQ);

	boost::optional<FormulaT> result = encoder.encode(constraint);

	if (!result) {
		BOOST_FAIL("result != {} expected, but got {}.");
	}

	FormulaT expected = FormulaT(carl::FormulaType::AND, FormulaT(carl::FormulaType::OR, FormulaT(x), FormulaT(y)), FormulaT(carl::FormulaType::OR, !FormulaT(x), !FormulaT(y)));

	BOOST_TEST(expected == *result, "expected " << expected << " but got " << result);
}

BOOST_AUTO_TEST_CASE(CardinalityEncoder_Simple3)
{
	carl::Variable x = carl::freshBooleanVariable("y");
	carl::Variable y = carl::freshBooleanVariable("y");
	
	ConstraintT constraint = ConstraintT(Poly(x) + Poly(y) + Rational(-1), carl::Relation::LEQ);

	boost::optional<FormulaT> result = encoder.encode(constraint);

	if (!result) {
		BOOST_FAIL("result != {} expected, but got {}.");
	}

	FormulaT expected = FormulaT(carl::FormulaType::AND, FormulaT(carl::FormulaType::OR, FormulaT(x), FormulaT(y)), FormulaT(carl::FormulaType::OR, !FormulaT(x), !FormulaT(y)));

	BOOST_TEST(expected == *result, "expected " << expected << " but got " << result);
}

BOOST_AUTO_TEST_CASE(CardinalityEncoder_Simple4)
{
	carl::Variable x = carl::freshBooleanVariable("y");
	carl::Variable y = carl::freshBooleanVariable("y");
	
	ConstraintT constraint = ConstraintT(Poly(x) + Poly(y) + Rational(-1), carl::Relation::LEQ);

	boost::optional<FormulaT> result = encoder.encode(constraint);

	if (!result) {
		BOOST_FAIL("result != {} expected, but got {}.");
	}

	FormulaT expected = FormulaT(carl::FormulaType::AND, FormulaT(carl::FormulaType::OR, FormulaT(x), FormulaT(y)), FormulaT(carl::FormulaType::OR, !FormulaT(x), !FormulaT(y)));

	BOOST_TEST(expected == *result, "expected " << expected << " but got " << result);
}

BOOST_AUTO_TEST_CASE(CardinalityEncoder_Simple5)
{
	carl::Variable x = carl::freshBooleanVariable("y");
	carl::Variable y = carl::freshBooleanVariable("y");
	
	ConstraintT constraint = ConstraintT(Poly(x) + Poly(y) + Rational(-1), carl::Relation::LEQ);

	boost::optional<FormulaT> result = encoder.encode(constraint);

	if (!result) {
		BOOST_FAIL("result != {} expected, but got {}.");
	}

	FormulaT expected = FormulaT(carl::FormulaType::AND, FormulaT(carl::FormulaType::OR, FormulaT(x), FormulaT(y)), FormulaT(carl::FormulaType::OR, !FormulaT(x), !FormulaT(y)));

	BOOST_TEST(expected == *result, "expected " << expected << " but got " << result);
}

BOOST_AUTO_TEST_CASE(CardinalityEncoder_Simple6)
{
	carl::Variable x = carl::freshBooleanVariable("y");
	carl::Variable y = carl::freshBooleanVariable("y");
	
	ConstraintT constraint = ConstraintT(Poly(x) + Poly(y) + Rational(-1), carl::Relation::LEQ);

	boost::optional<FormulaT> result = encoder.encode(constraint);

	if (!result) {
		BOOST_FAIL("result != {} expected, but got {}.");
	}

	FormulaT expected = FormulaT(carl::FormulaType::AND, FormulaT(carl::FormulaType::OR, FormulaT(x), FormulaT(y)), FormulaT(carl::FormulaType::OR, !FormulaT(x), !FormulaT(y)));

	BOOST_TEST(expected == *result, "expected " << expected << " but got " << result);
}

// BOOST_AUTO_TEST_CASE(Test_CAD)
// {
// 	carl::Variable x = carl::freshRealVariable("x");
// 	carl::Variable y = carl::freshRealVariable("y");
// 	Poly p = Poly(x*y)+Poly(y)+Rational(1);
// 	Poly q = Poly(y*y*y)+Poly(x*x*y)+Rational(2);
// 	
// 	CAD<NewCADSettingsSO> cad;
// 	cad.reset({x,y});
// 	cad.addConstraint(ConstraintT(p, carl::Relation::GEQ));
// 	cad.addConstraint(ConstraintT(q, carl::Relation::LEQ));
// 	
// 	Assignment a;
// 	std::vector<FormulaSetT> mis;
// 	cad.check(a, mis);
// }

BOOST_AUTO_TEST_SUITE_END();
BOOST_AUTO_TEST_SUITE_END();
