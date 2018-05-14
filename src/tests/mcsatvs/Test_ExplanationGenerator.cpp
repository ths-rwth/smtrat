#include <boost/test/unit_test.hpp>


#include <lib/datastructures/mcsat/vs/ExplanationGenerator.h>
#include <lib/logging.h>

using namespace smtrat;
using namespace mcsat::vs::helper;

BOOST_AUTO_TEST_SUITE(Test_ExplanationGenerator);

BOOST_AUTO_TEST_CASE(Test_generateZeros_eliminationVariableNotContained) {
	carl::Variable x = carl::freshRealVariable("x");
	carl::Variable y = carl::freshRealVariable("y");

	ConstraintT c1(Poly(x)+Rational(1), carl::Relation::LEQ);
	bool result = generateZeros(c1, y, [&](const SqrtEx&& sqrtExpression, const ConstraintsT&& sideConditions) {
    	BOOST_CHECK(false);
    });
	BOOST_CHECK(result);
}
BOOST_AUTO_TEST_CASE(Test_generateZeros_degreeTooHigh) {
	carl::Variable x = carl::freshRealVariable("x");
	carl::Variable y = carl::freshRealVariable("y");

	ConstraintT c1(Poly(y)*y*y+Rational(1), carl::Relation::LEQ);
	bool result = generateZeros(c1, y, [&](const SqrtEx&& sqrtExpression, const ConstraintsT&& sideConditions) {
    	BOOST_CHECK(false);
    });
	BOOST_CHECK(result == false);

	int zeros = 0;
	ConstraintT c2(Poly(y)*y*x, carl::Relation::LEQ);
	result = generateZeros(c2, y, [&](const SqrtEx&& sqrtExpression, const ConstraintsT&& sideConditions) {
    	zeros++;
    });
	BOOST_CHECK(result == true);
	BOOST_CHECK(zeros > 0);
}
BOOST_AUTO_TEST_CASE(Test_generateZeros_deg1) {
	carl::Variable x = carl::freshRealVariable("x");
	carl::Variable y = carl::freshRealVariable("y");

	ConstraintT c1(Rational(0)*Poly(y), carl::Relation::LESS);
	bool result = generateZeros(c1, y, [&](const SqrtEx&& sqrtExpression, const ConstraintsT&& sideConditions) {
    	BOOST_CHECK(false);
    });
	BOOST_CHECK(result);

	ConstraintT c2(Poly(y)*x+Rational(1), carl::Relation::EQ);
	result = generateZeros(c2, y, [&](const SqrtEx&& sqrtExpression, const ConstraintsT&& sideConditions) {
    	BOOST_CHECK(sqrtExpression==SqrtEx(Poly(-1), ZERO_POLYNOMIAL, Poly(x), ZERO_POLYNOMIAL));
		BOOST_CHECK(sideConditions.size() == 1);
		BOOST_CHECK(*sideConditions.begin() == ConstraintT(Poly(x), carl::Relation::NEQ));
    });
	BOOST_CHECK(result);
}
BOOST_AUTO_TEST_CASE(Test_generateZeros_deg2) {
	carl::Variable x = carl::freshRealVariable("x");
	carl::Variable y = carl::freshRealVariable("y");

	ConstraintT c1(Poly(y)*y+Rational(1), carl::Relation::EQ);
	bool result = generateZeros(c1, y, [&](const SqrtEx&& sqrtExpression, const ConstraintsT&& sideConditions) {
    	BOOST_CHECK(false);
    });
	BOOST_CHECK(result);

	ConstraintT c2(Poly(y)*y+y+x, carl::Relation::EQ);
	int resultcount = 0;
	result = generateZeros(c2, y, [&](const SqrtEx&& sqrtExpression, const ConstraintsT&& sideConditions) {
		BOOST_CHECK(sqrtExpression==SqrtEx(Poly(Rational(-1)), ONE_POLYNOMIAL, Poly(Rational(2)), Poly(Rational(1))-Rational(4)*x) || sqrtExpression==SqrtEx(Poly(Rational(-1)), MINUS_ONE_POLYNOMIAL, Poly(Rational(2)), Poly(Rational(1))-Rational(4)*x));
		BOOST_CHECK(sideConditions.size() == 1);
		BOOST_CHECK(*sideConditions.begin() == ConstraintT(Poly(Rational(1))-Rational(4)*x, carl::Relation::GEQ));
		resultcount++;
    });
	BOOST_CHECK(resultcount == 2);
	BOOST_CHECK(result);
}

BOOST_AUTO_TEST_CASE(Test_doccToFormula) {
	carl::Variable x = carl::freshRealVariable("x");
	::vs::DisjunctionOfConstraintConjunctions docc;
	::vs::ConstraintVector conjunction1;
	conjunction1.push_back(ConstraintT(Poly(x), carl::Relation::EQ));
	conjunction1.push_back(ConstraintT(Poly(x)+Rational(1), carl::Relation::EQ));
	::vs::ConstraintVector conjunction2;
	conjunction2.push_back(ConstraintT(Poly(x)+Rational(2), carl::Relation::EQ));
	conjunction2.push_back(ConstraintT(Poly(x)+Rational(3), carl::Relation::EQ));
	docc.push_back(conjunction1);
	docc.push_back(conjunction2);

	FormulaT formula = doccToFormula(docc);
	std::stringstream ss;
	ss << formula;
	BOOST_CHECK(ss.str() == "(or (and (= x 0) (= (+ x 1) 0)) (and (= (+ x 2) 0) (= (+ x 3) 0)))");
}

BOOST_AUTO_TEST_CASE(Test_generateTestCandidates_degreeTooHigh) {
	carl::Variable x = carl::freshRealVariable("x");
	carl::Variable y = carl::freshRealVariable("y");
	std::vector<::vs::Substitution> results;

	ConstraintT c1(Poly(y)*y*y+Rational(1), carl::Relation::EQ);
	std::vector<const ConstraintT*> constraints1;
	constraints1.push_back(&c1);

	bool status = generateTestCandidates(results, y, constraints1);
	BOOST_CHECK(!status);

	ConstraintT c2(Poly(y)*y+Rational(1), carl::Relation::EQ);
	std::vector<const ConstraintT*> constraints2;
	constraints2.push_back(&c2);

	status = generateTestCandidates(results, y, constraints2);
	BOOST_CHECK(status);
}
BOOST_AUTO_TEST_CASE(Test_generateTestCandidates_variableNotIncluded) {
	carl::Variable x = carl::freshRealVariable("x");
	carl::Variable y = carl::freshRealVariable("y");
	std::vector<::vs::Substitution> results;

	ConstraintT c(Poly(x), carl::Relation::EQ);
	std::vector<const ConstraintT*> constraints;
	constraints.push_back(&c);

	bool status = generateTestCandidates(results, y, constraints);
	BOOST_CHECK(status);
	BOOST_CHECK(results.size() == 1); // only y -> -infty
}
BOOST_AUTO_TEST_CASE(Test_generateTestCandidates_constraintType) {
	carl::Variable x = carl::freshRealVariable("x");
	carl::Variable y = carl::freshRealVariable("y");
	std::vector<::vs::Substitution> results;

	ConstraintT c1(Poly(y), carl::Relation::GEQ);
	ConstraintT c2(Poly(y), carl::Relation::GREATER);
	std::vector<const ConstraintT*> constraints;
	constraints.push_back(&c1);
	constraints.push_back(&c2);

	bool status = generateTestCandidates(results, y, constraints);
	BOOST_CHECK(status);
	BOOST_CHECK(results.size() == 3);
	BOOST_CHECK(results[1].type() == ::vs::Substitution::Type::NORMAL);
	BOOST_CHECK(results[2].type() == ::vs::Substitution::Type::PLUS_EPSILON);
}
BOOST_AUTO_TEST_CASE(Test_generateTestCandidates_duplicateRemoval) {
	carl::Variable x = carl::freshRealVariable("x");
	carl::Variable y = carl::freshRealVariable("y");
	std::vector<::vs::Substitution> results;

	ConstraintT c1(Poly(y) - x, carl::Relation::GEQ);
	ConstraintT c2(Poly(y) - x, carl::Relation::GEQ);
	std::vector<const ConstraintT*> constraints;
	constraints.push_back(&c1);
	constraints.push_back(&c2);

	bool status = generateTestCandidates(results, y, constraints);
	BOOST_CHECK(status);
	BOOST_CHECK(results.size() == 2); // duplicates removed
}

BOOST_AUTO_TEST_CASE(Test_getExplanation_degreeTooHigh) {
	carl::Variable x = carl::freshRealVariable("x");
	carl::Variable y = carl::freshRealVariable("y");
	std::vector<carl::Variable> ordering;
	ordering.push_back(x);
	ordering.push_back(y);

	ConstraintT c1(Poly(y)*y*y+Rational(1), carl::Relation::EQ);
	FormulaT f1(c1);
	std::vector<FormulaT> constraints;
	constraints.push_back(f1);

	Model varModel;
	varModel.emplace(x, Rational(0));

	mcsat::vs::ExplanationGenerator generator(constraints, ordering, y, varModel);
	boost::optional<FormulaT> result = generator.getExplanation(FormulaT(carl::FormulaType::FALSE));
	BOOST_CHECK(!result);	
}
BOOST_AUTO_TEST_CASE(Test_getExplanation_substitution) {
	carl::Variable x = carl::freshRealVariable("x");
	carl::Variable y = carl::freshRealVariable("y");
	std::vector<carl::Variable> ordering;
	ordering.push_back(x);
	ordering.push_back(y);

	std::vector<FormulaT> constraints;
	ConstraintT c1((Poly(x)-Rational(2)).pow(2) + (Poly(y)-Rational(2)).pow(2) - Rational(1), carl::Relation::LESS);
	constraints.push_back(FormulaT(c1));
	ConstraintT c2(Poly(x)-y, carl::Relation::EQ);
	constraints.push_back(FormulaT(c2));

	Model varModel;
	varModel.emplace(x, Rational(0));

	mcsat::vs::ExplanationGenerator generator(constraints, ordering, y, varModel);
	boost::optional<FormulaT> result = generator.getExplanation(FormulaT(carl::FormulaType::FALSE));
	BOOST_CHECK(result);
	std::stringstream ss;
	ss << result.value();
	BOOST_CHECK(ss.str() == "(or (<= (+ (* (- 1) (* y y)) (* 4 y) (* (- 1) (* x x)) (* 4 x) (- 7)) 0) (!= (+ y (* (- 1) x)) 0) (< (+ (* 2 (* x x)) (* (- 8) x) 7) 0))");
}


BOOST_AUTO_TEST_SUITE_END();