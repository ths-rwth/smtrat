#include <boost/test/unit_test.hpp>
#include <boost/optional/optional_io.hpp>

#include <iostream>

#include "../../lib/modules/PBPPModule/CardinalityEncoder.h"

using namespace smtrat;

/**
 * Description of test cases for cardinality:
 * 1. x1 + x2 - 1 <= 0 -> (x1 or x2) and (!x1 or !x2)
 * 2. exactly
 * 3. atleast
 * 4. atmost
 * 5. long formula
 * 6. true evaluating
 * 7. false evaluating
 */
struct CardinalityFixture {
    CardinalityFixture() { }

    CardinalityEncoder encoder;
};

BOOST_FIXTURE_TEST_SUITE( s, CardinalityFixture )

BOOST_AUTO_TEST_SUITE( CardinalityEncoder )

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
	BOOST_TEST_MESSAGE(expected);

	BOOST_TEST(expected == *result, "expected " << expected << " but got " << result);
}

BOOST_AUTO_TEST_CASE( CardinalityEncoder_Simple_EQ )
{
	carl::Variable x = carl::freshBooleanVariable("x");
	carl::Variable y = carl::freshBooleanVariable("y");
	
	ConstraintT constraint = ConstraintT(Poly(x) + Poly(y) + Rational(-1), carl::Relation::EQ);

	boost::optional<FormulaT> result = encoder.encode(constraint);

	if (!result) {
		BOOST_FAIL("result != {} expected, but got {}.");
	}

	FormulaT expected = FormulaT(carl::FormulaType::AND, FormulaT(carl::FormulaType::OR, FormulaT(x), !FormulaT(y)), FormulaT(carl::FormulaType::OR, !FormulaT(x), FormulaT(y)));
	BOOST_TEST_MESSAGE(expected);

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
	BOOST_TEST_MESSAGE(expected);

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
	BOOST_TEST_MESSAGE(expected);

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
	BOOST_TEST_MESSAGE(expected);

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
	BOOST_TEST_MESSAGE(expected);

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
	BOOST_TEST_MESSAGE(expected);

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
	BOOST_TEST_MESSAGE(expected);

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
	BOOST_TEST_MESSAGE(expected);

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
	BOOST_TEST_MESSAGE(expected);

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
	BOOST_TEST_MESSAGE(expected);

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
