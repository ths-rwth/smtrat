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

BOOST_AUTO_TEST_CASE( CardinalityEncoder_Single_Literal_False )
{
	carl::Variable x = carl::freshBooleanVariable("x");
	
	ConstraintT constraint = ConstraintT(Poly(x), carl::Relation::EQ);

	boost::optional<FormulaT> result = encoder.encode(constraint);

	if (!result) {
		BOOST_FAIL("result != {} expected, but got {}.");
	}

	FormulaT expected = FormulaT(carl::FormulaType::NOT, FormulaT(x));

	BOOST_TEST((expected == *result), "expected " << expected << " but got " << result);
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

	FormulaT expected = FormulaT(carl::FormulaType::OR, FormulaT(carl::FormulaType::AND, FormulaT(x), !FormulaT(y)), FormulaT(carl::FormulaType::AND, !FormulaT(x), FormulaT(y)));

	BOOST_TEST((expected == *result), "expected " << expected << " but got " << result);
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

	BOOST_TEST((expected == *result), "expected " << expected << " but got " << result);
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

	BOOST_TEST((expected == *result), "expected " << expected << " but got " << result);
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

	BOOST_TEST((expected == *result), "expected " << expected << " but got " << result);
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

	BOOST_TEST((expected == *result), "expected " << expected << " but got " << result);
}

// END TEST SUITE EQ
BOOST_AUTO_TEST_SUITE_END();

BOOST_AUTO_TEST_CASE( CardinalityEncoder_Simple_LEQ_Coeff_LESS_CONST )
{
	carl::Variable x = carl::freshBooleanVariable("x");
	carl::Variable y = carl::freshBooleanVariable("y");
	carl::Variable z = carl::freshBooleanVariable("z");

	ConstraintT constraint = ConstraintT(Poly(x) + Poly(y) + Poly(z) - Rational(4), carl::Relation::LEQ);

	boost::optional<FormulaT> result = encoder.encode(constraint);

	if (!result) {
		BOOST_FAIL("result != {} expected, but got {}.");
	}

	// since 0 <= 4 is of course true as well
	FormulaT expected = FormulaT(carl::FormulaType::TRUE);

	BOOST_TEST((expected == *result), "expected " << expected << " but got " << result);
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

	FormulaT expected = FormulaT(carl::FormulaType::OR,
			FormulaT(carl::FormulaType::AND, !FormulaT(x), !FormulaT(y)),
			FormulaT(carl::FormulaType::AND, !FormulaT(x), FormulaT(y)),
			FormulaT(carl::FormulaType::AND, FormulaT(x), !FormulaT(y)));

	BOOST_TEST((expected == *result), "expected " << expected << " but got " << result);
}


BOOST_AUTO_TEST_CASE(CardinalityEncoder_PositiveCoeff_AtMost)
{
	carl::Variable x1 = carl::freshBooleanVariable("x1");
	carl::Variable x2 = carl::freshBooleanVariable("x2");
	carl::Variable x3 = carl::freshBooleanVariable("x3");

	// x1 + x2 + x3 + x4 <= 2
	ConstraintT constraint = ConstraintT(Poly(x1) + Poly(x2) + Poly(x3) + Rational(-2), carl::Relation::LEQ);

	boost::optional<FormulaT> result = encoder.encode(constraint);

	if (!result) {
		BOOST_FAIL("result != {} expected, but got {}.");
	}

	FormulasT conjunctions;
	// none
	conjunctions.push_back(FormulaT(carl::FormulaType::AND, !FormulaT(x1), !FormulaT(x2), !FormulaT(x3)));
	// one
	conjunctions.push_back(FormulaT(carl::FormulaType::AND, FormulaT(x1), !FormulaT(x2), !FormulaT(x3)));
	conjunctions.push_back(FormulaT(carl::FormulaType::AND, !FormulaT(x1), FormulaT(x2), !FormulaT(x3)));
	conjunctions.push_back(FormulaT(carl::FormulaType::AND, !FormulaT(x1), !FormulaT(x2), FormulaT(x3)));
	// two
	conjunctions.push_back(FormulaT(carl::FormulaType::AND, FormulaT(x1), FormulaT(x2), !FormulaT(x3)));
	conjunctions.push_back(FormulaT(carl::FormulaType::AND, FormulaT(x1), !FormulaT(x2), FormulaT(x3)));
	conjunctions.push_back(FormulaT(carl::FormulaType::AND, !FormulaT(x1), FormulaT(x2), FormulaT(x3)));
	
	FormulaT expected = FormulaT(carl::FormulaType::OR, conjunctions);

	BOOST_TEST((expected == *result), "expected " << expected << " but got " << result);
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

	FormulasT conjunctions;
	conjunctions.push_back(FormulaT(carl::FormulaType::AND, !FormulaT(x1), !FormulaT(x2), !FormulaT(x3)));
	conjunctions.push_back(FormulaT(carl::FormulaType::AND, FormulaT(x1), !FormulaT(x2), !FormulaT(x3)));
	conjunctions.push_back(FormulaT(carl::FormulaType::AND, !FormulaT(x1), FormulaT(x2), !FormulaT(x3)));
	conjunctions.push_back(FormulaT(carl::FormulaType::AND, !FormulaT(x1), !FormulaT(x2), FormulaT(x3)));
	conjunctions.push_back(FormulaT(carl::FormulaType::AND, FormulaT(x1), FormulaT(x2), !FormulaT(x3)));
	conjunctions.push_back(FormulaT(carl::FormulaType::AND, FormulaT(x1), !FormulaT(x2), FormulaT(x3)));
	conjunctions.push_back(FormulaT(carl::FormulaType::AND, !FormulaT(x1), FormulaT(x2), FormulaT(x3)));
	
	FormulaT expected = FormulaT(carl::FormulaType::OR, conjunctions);

	BOOST_TEST((expected == *result), "expected " << expected << " but got " << result);
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

	BOOST_TEST((expected == *result), "expected " << expected << " but got " << result);
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

	FormulaT expected = FormulaT(carl::FormulaType::FALSE);

	BOOST_TEST((expected == *result), "expected " << expected << " but got " << result);
}

BOOST_AUTO_TEST_CASE(CardinalityEncoder_AtLeast_False)
{
	carl::Variable x1 = carl::freshBooleanVariable("x1");
	carl::Variable x2 = carl::freshBooleanVariable("x2");
	carl::Variable x3 = carl::freshBooleanVariable("x3");

	ConstraintT constraint = ConstraintT(-Poly(x1) - Poly(x2) - Poly(x3) - Rational(-4), carl::Relation::LEQ);

	boost::optional<FormulaT> result = encoder.encode(constraint);

	if (!result) {
		BOOST_FAIL("result != {} expected, but got {}.");
	}

	FormulaT expected = FormulaT(carl::FormulaType::FALSE);

	BOOST_TEST((expected == *result), "expected " << expected << " but got " << result);
}

BOOST_AUTO_TEST_CASE(CardinalityEncoder_AtLeast)
{
	carl::Variable x1 = carl::freshBooleanVariable("x1");
	carl::Variable x2 = carl::freshBooleanVariable("x2");
	carl::Variable x3 = carl::freshBooleanVariable("x3");

	ConstraintT constraint = ConstraintT(-Poly(x1) - Poly(x2) - Poly(x3) - Rational(-1), carl::Relation::LEQ);

	boost::optional<FormulaT> result = encoder.encode(constraint);

	if (!result) {
		BOOST_FAIL("result != {} expected, but got {}.");
	}

	FormulaT expected = FormulaT(carl::FormulaType::OR,
			FormulaT(x1),
			FormulaT(x2),
			FormulaT(x3));

	BOOST_TEST((expected == *result), "expected " << expected << " but got " << result);
}

BOOST_AUTO_TEST_CASE(CardinalityEncoder_AtLeast_2)
{
	carl::Variable x1 = carl::freshBooleanVariable("x1");
	carl::Variable x2 = carl::freshBooleanVariable("x2");
	carl::Variable x3 = carl::freshBooleanVariable("x3");

	ConstraintT constraint = ConstraintT(-Poly(x1) - Poly(x2) - Poly(x3) - Rational(-2), carl::Relation::LEQ);

	boost::optional<FormulaT> result = encoder.encode(constraint);

	if (!result) {
		BOOST_FAIL("result != {} expected, but got {}.");
	}

	FormulaT expected = FormulaT(carl::FormulaType::AND,
			// anything but at least one
			FormulaT(carl::FormulaType::OR, FormulaT(x1), FormulaT(x2), FormulaT(x3)),
			// and not not exactly 1
			!FormulaT(carl::FormulaType::OR,
				FormulaT(carl::FormulaType::AND, FormulaT(x1), !FormulaT(x2), !FormulaT(x3)),
				FormulaT(carl::FormulaType::AND, !FormulaT(x1), FormulaT(x2), !FormulaT(x3)),
				FormulaT(carl::FormulaType::AND, !FormulaT(x1), !FormulaT(x2), FormulaT(x3)))
			);

	BOOST_TEST((expected == *result), "expected " << expected << " but got " << result);
}

BOOST_AUTO_TEST_SUITE_END();
BOOST_AUTO_TEST_SUITE_END();
