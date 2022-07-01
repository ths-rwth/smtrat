#include <boost/test/unit_test.hpp>


#include <smtrat-mcsat/explanations/vs/ExplanationGenerator.h>
#include <smtrat-common/smtrat-common.h>

using namespace smtrat;
using namespace mcsat::vs::helper;

BOOST_AUTO_TEST_SUITE(Test_ExplanationGenerator);

BOOST_AUTO_TEST_CASE(Test_generateZeros_eliminationVariableNotContained) {
	carl::Variable x = carl::fresh_real_variable("x");
	carl::Variable y = carl::fresh_real_variable("y");

	ConstraintT c1(Poly(x)+Rational(1), carl::Relation::LEQ);
	bool result = generateZeros(c1, y, [&](const SqrtEx&& sqrtExpression, const ConstraintsT&& sideConditions) {
    	BOOST_CHECK(false);
    });
	BOOST_CHECK(result);
}
BOOST_AUTO_TEST_CASE(Test_generateZeros_degreeTooHigh) {
	carl::Variable x = carl::fresh_real_variable("x");
	carl::Variable y = carl::fresh_real_variable("y");

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
	carl::Variable x = carl::fresh_real_variable("x");
	carl::Variable y = carl::fresh_real_variable("y");

	ConstraintT c1(Rational(0)*Poly(y), carl::Relation::LESS);
	bool result = generateZeros(c1, y, [&](const SqrtEx&& sqrtExpression, const ConstraintsT&& sideConditions) {
    	BOOST_CHECK(false);
    });
	BOOST_CHECK(result);

	ConstraintT c2(Poly(y)*x+Rational(1), carl::Relation::EQ);
	result = generateZeros(c2, y, [&](const SqrtEx&& sqrtExpression, const ConstraintsT&& sideConditions) {
    	BOOST_CHECK(sqrtExpression==SqrtEx(Poly(-1), Poly(0), Poly(x), Poly(0)));
		BOOST_CHECK(sideConditions.size() == 1);
		BOOST_CHECK(*sideConditions.begin() == ConstraintT(Poly(x), carl::Relation::NEQ));
    });
	BOOST_CHECK(result);
}
BOOST_AUTO_TEST_CASE(Test_generateZeros_deg2) {
	carl::Variable x = carl::fresh_real_variable("x");
	carl::Variable y = carl::fresh_real_variable("y");

	ConstraintT c1(Poly(y)*y+Rational(1), carl::Relation::EQ);
	bool result = generateZeros(c1, y, [&](const SqrtEx&& sqrtExpression, const ConstraintsT&& sideConditions) {
    	BOOST_CHECK(false);
    });
	BOOST_CHECK(result);

	ConstraintT c2(Poly(y)*y+y+x, carl::Relation::EQ);
	int resultcount = 0;
	result = generateZeros(c2, y, [&](const SqrtEx&& sqrtExpression, const ConstraintsT&& sideConditions) {
		BOOST_CHECK(sqrtExpression==SqrtEx(Poly(Rational(-1)), Poly(1), Poly(Rational(2)), Poly(Rational(1))-Rational(4)*x) || sqrtExpression==SqrtEx(Poly(Rational(-1)), Poly(-1), Poly(Rational(2)), Poly(Rational(1))-Rational(4)*x));
		BOOST_CHECK(sideConditions.size() == 1);
		BOOST_CHECK(*sideConditions.begin() == ConstraintT(Poly(Rational(1))-Rational(4)*x, carl::Relation::GEQ));
		resultcount++;
    });
	BOOST_CHECK(resultcount == 2);
	BOOST_CHECK(result);
}

BOOST_AUTO_TEST_CASE(Test_generateZeros_VarComp_eliminationVariableNotContained) {
	carl::Variable x = carl::fresh_real_variable("x");
	carl::Variable y = carl::fresh_real_variable("y");

	VariableComparisonT varcomp(x, MultivariateRootT(Poly(x)+Rational(1), 1), carl::Relation::EQ);
	Model model;

	bool result = generateZeros(varcomp, y, model, [&](const SqrtEx&& sqrtExpression, const ConstraintsT&& sideConditions) {
    	BOOST_CHECK(false);
    });
	BOOST_CHECK(result);
}
BOOST_AUTO_TEST_CASE(Test_generateZeros_VarComp_MVRoot_degreeTooHigh) {
	carl::Variable x = carl::fresh_real_variable("x");
	carl::Variable y = carl::fresh_real_variable("y");
	VariableComparisonT varcomp(y, MultivariateRootT(Poly(y)*y*y*x-Rational(1), 2, y), carl::Relation::EQ);

	Model model;

	bool result = generateZeros(varcomp, y, model, [&](const SqrtEx&& sqrtExpression, const ConstraintsT&& sideConditions) {
    	BOOST_CHECK(false);
    });
	BOOST_CHECK(!result);
}
BOOST_AUTO_TEST_CASE(Test_generateZeros_VarComp_MVRoot_simple) {
	carl::Variable x = carl::fresh_real_variable("x");
	carl::Variable y = carl::fresh_real_variable("y");
	VariableComparisonT varcomp(y, MultivariateRootT(Poly(y)*y*x-Rational(1), 2, y), carl::Relation::EQ);

	Model model;
	model.assign(x, Rational(1));
	bool result = generateZeros(varcomp, y, model, [&](const SqrtEx&& sqrtExpression, const ConstraintsT&& sideConditions) {
		// 0+1*sqrt(x)/(x)
    	BOOST_CHECK(sqrtExpression == SqrtEx(Poly(Rational(0)), Poly(Rational(1)), Poly(x), Poly(x)));
		BOOST_CHECK(sideConditions.size() > 0);
    });
	BOOST_CHECK(result);
}
BOOST_AUTO_TEST_CASE(Test_generateZeros_VarComp_MVRoot_multivar) {
	carl::Variable x1 = carl::fresh_real_variable("x1");
	carl::Variable x2 = carl::fresh_real_variable("x2");
	carl::Variable y = carl::fresh_real_variable("y");
	Poly poly = (Poly(y)*x1) + (Poly(y)*y*x2);
	VariableComparisonT varcomp(y, MultivariateRootT(poly, 2, y), carl::Relation::EQ);

	Model model;
	model.assign(x1, Rational(-1));
	model.assign(x2, Rational(1));

	bool result = generateZeros(varcomp, y, model, [&](const SqrtEx&& sqrtExpression, const ConstraintsT&& sideConditions) {
		// ((-1)*x1)/(x2)
    	BOOST_CHECK(sqrtExpression == SqrtEx(Poly(Rational(0)), Poly(Rational(-1))*x1, Poly(x2), Poly(Rational(1))));
		BOOST_CHECK(sideConditions.size() > 0);
    });
	BOOST_CHECK(result);
}
BOOST_AUTO_TEST_CASE(Test_generateZeros_VarComp_RAN_simple) {
	carl::Variable r = carl::fresh_real_variable("r");
	carl::UnivariatePolynomial<Rational> pol = carl::to_univariate_polynomial(Poly(r)*r-Rational(2));
	carl::Interval<Rational> interval(Rational(1), carl::BoundType::STRICT, Rational(2), carl::BoundType::STRICT);
	auto ran = carl::RealAlgebraicNumber<Rational>::create_safe(pol, interval);

	bool result = generateZeros(ran, [&](const SqrtEx&& sqrtExpression, const ConstraintsT&& sideConditions) {
		// sqrt(2) = 0+1*sqrt(8)/2
    	BOOST_CHECK(sqrtExpression == SqrtEx(Poly(Rational(0)), Poly(Rational(1)), Poly(Rational(2)), Poly(Rational(8))));
    });
	BOOST_CHECK(result);
}

BOOST_AUTO_TEST_CASE(Test_compareSqrtEx) {
	carl::Variable x = carl::fresh_real_variable("x");
	SqrtEx sqrtA(Poly(Rational(0)), Poly(Rational(1))*x, Poly(Rational(1)), Poly(Rational(1)));
	SqrtEx sqrtB(Poly(Rational(0)), Poly(Rational(-1))*x, Poly(Rational(1)), Poly(Rational(1)));
	Model model1;
	model1.assign(x, Rational(-1));
	Model model2;
	model2.assign(x, Rational(1));

	BOOST_CHECK(compareSqrtEx(sqrtA, sqrtB, model1).value());
	BOOST_CHECK(!compareSqrtEx(sqrtB, sqrtA, model1).value());
	BOOST_CHECK(!compareSqrtEx(sqrtA, sqrtB, model2).value());
	BOOST_CHECK(compareSqrtEx(sqrtB, sqrtA, model2).value());
}

BOOST_AUTO_TEST_CASE(Test_compareSqrtExWithRational) {
	SqrtEx sqrtB(Poly(Rational(0)), Poly(Rational(-1)), Poly(Rational(10)), Poly(Rational(40)));
	
	Rational lower = Rational(-16) / Rational(25);
	Rational upper = Rational(-31) / Rational(50);

	Model model;

	BOOST_CHECK(rationalLessThanSqrtEx(lower, sqrtB, model));
	BOOST_CHECK(!rationalLessThanSqrtEx(upper, sqrtB, model));
	BOOST_CHECK(!sqrtExLessThanRational(sqrtB, lower, model));
	BOOST_CHECK(sqrtExLessThanRational(sqrtB, upper, model));
}

BOOST_AUTO_TEST_CASE(Test_compareSqrtExWithRational_fraction) {
	SqrtEx sqrtB(Poly(Rational(2)), Poly(Rational(0)), Poly(Rational(10)), Poly(Rational(0)));
	
	Rational lower = Rational(1) / Rational(10);
	Rational upper = Rational(3) / Rational(10);

	Model model;

	BOOST_CHECK(rationalLessThanSqrtEx(lower, sqrtB, model));
	BOOST_CHECK(!rationalLessThanSqrtEx(upper, sqrtB, model));
	BOOST_CHECK(!sqrtExLessThanRational(sqrtB, lower, model));
	BOOST_CHECK(sqrtExLessThanRational(sqrtB, upper, model));
}

BOOST_AUTO_TEST_CASE(Test_doccToFormula) {
	carl::Variable x = carl::fresh_real_variable("x");
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
	carl::Variable x = carl::fresh_real_variable("x");
	carl::Variable y = carl::fresh_real_variable("y");
	std::vector<::vs::Substitution> results;

	ConstraintT c1(Poly(y)*y*y+Rational(1), carl::Relation::EQ);
	FormulaSetT constraints1;
	constraints1.emplace(c1);

	bool status = generateTestCandidates(results, y, Model(), constraints1);
	BOOST_CHECK(!status);

	ConstraintT c2(Poly(y)*y+Rational(1), carl::Relation::GEQ);
	FormulaSetT constraints2;
	constraints2.emplace(c2);

	status = generateTestCandidates(results, y, Model(), constraints2);
	BOOST_CHECK(status);
}
BOOST_AUTO_TEST_CASE(Test_generateTestCandidates_variableNotIncluded) {
	carl::Variable x = carl::fresh_real_variable("x");
	carl::Variable y = carl::fresh_real_variable("y");
	std::vector<::vs::Substitution> results;

	ConstraintT c(Poly(x), carl::Relation::EQ);
	FormulaSetT constraints;
	constraints.emplace(c);

	bool status = generateTestCandidates(results, y, Model(), constraints);
	BOOST_CHECK(status);
	BOOST_CHECK(results.size() == 1); // only y -> -infty
}
BOOST_AUTO_TEST_CASE(Test_generateTestCandidates_constraintType) {
	carl::Variable x = carl::fresh_real_variable("x");
	carl::Variable y = carl::fresh_real_variable("y");
	std::vector<::vs::Substitution> results;

	ConstraintT c1(Poly(y), carl::Relation::GEQ);
	ConstraintT c2(Poly(y), carl::Relation::GREATER);
	FormulaSetT constraints;
	constraints.emplace(c1);
	constraints.emplace(c2);

	bool status = generateTestCandidates(results, y, Model(), constraints);
	BOOST_CHECK(status);
	BOOST_CHECK(results.size() == 3);
	BOOST_CHECK(results[1].type() == ::vs::Substitution::Type::NORMAL);
	BOOST_CHECK(results[2].type() == ::vs::Substitution::Type::PLUS_EPSILON);
}
BOOST_AUTO_TEST_CASE(Test_generateTestCandidates_duplicateRemoval) {
	carl::Variable x = carl::fresh_real_variable("x");
	carl::Variable y = carl::fresh_real_variable("y");
	std::vector<::vs::Substitution> results;

	ConstraintT c1(Poly(y) - x, carl::Relation::GEQ);
	ConstraintT c2(Poly(y) - x, carl::Relation::GEQ);
	FormulaSetT constraints;
	constraints.emplace(c1);
	constraints.emplace(c2);

	bool status = generateTestCandidates(results, y, Model(), constraints);
	BOOST_CHECK(status);
	BOOST_CHECK(results.size() == 2); // duplicates removed
}
BOOST_AUTO_TEST_CASE(Test_generateTestCandidates_variableComparison) {
	carl::Variable x = carl::fresh_real_variable("x");
	carl::Variable y = carl::fresh_real_variable("y");
	VariableComparisonT varcomp(y, MultivariateRootT(Poly(y)*y*x-Rational(1), 2, y), carl::Relation::EQ);
	Model model;
	model.assign(x, Rational(1));
	FormulaSetT constraints;
	constraints.emplace(varcomp);

	std::vector<::vs::Substitution> results;
	bool result = generateTestCandidates( results, y, model, constraints);
	BOOST_CHECK(result);
	BOOST_CHECK(results.size()==2);

	// 0+1*sqrt(x)/(x)
	// note that results[0] is -infty
    BOOST_CHECK(results[1].term() == SqrtEx(Poly(Rational(0)), Poly(Rational(1)), Poly(x), Poly(x)));
	BOOST_CHECK(results[1].sideCondition().size() > 0);
}

BOOST_AUTO_TEST_CASE(Test_substitute_constraint_varNotContained) {
	carl::Variable x = carl::fresh_real_variable("x");
	carl::Variable y = carl::fresh_real_variable("y");
	
	::vs::Substitution substitution(y, SqrtEx(Poly(Rational(1))), ::vs::Substitution::Type::NORMAL, carl::PointerSet<::vs::Condition>(), ConstraintsT());
	ConstraintT constraint(Poly(x), carl::Relation::EQ);

	FormulaT result;
	bool status = substitute(constraint, substitution, result);
	BOOST_CHECK(status);
	BOOST_CHECK(result.constraint() == constraint);
}
BOOST_AUTO_TEST_CASE(Test_substitute_constraint_simple) {
	carl::Variable y = carl::fresh_real_variable("y");
	
	::vs::Substitution substitution(y, SqrtEx(Poly(Rational(1))), ::vs::Substitution::Type::NORMAL, carl::PointerSet<::vs::Condition>(), ConstraintsT());
	ConstraintT constraint(Poly(y), carl::Relation::EQ);

	FormulaT result;
	bool status = substitute(constraint, substitution, result);
	BOOST_CHECK(status);
	BOOST_CHECK(result.type() == carl::FormulaType::FALSE);
}
BOOST_AUTO_TEST_CASE(Test_substitute_varComp_varNotContained) {
	carl::Variable x = carl::fresh_real_variable("x");
	carl::Variable y = carl::fresh_real_variable("y");

	carl::Variable r = carl::fresh_real_variable("r");
	carl::UnivariatePolynomial<Rational> pol = carl::to_univariate_polynomial(Poly(r)*r-Rational(2));
	carl::Interval<Rational> interval(Rational(1), carl::BoundType::STRICT, Rational(2), carl::BoundType::STRICT);
	auto ran = carl::RealAlgebraicNumber<Rational>::create_safe(pol, interval);
	
	::vs::Substitution substitution(y, SqrtEx(Poly(Rational(1))), ::vs::Substitution::Type::NORMAL, carl::PointerSet<::vs::Condition>(), ConstraintsT());
	VariableComparisonT varcomp(x, ran, carl::Relation::EQ);

	FormulaT result;
	bool status = substitute(varcomp, substitution, Model(), result);
	BOOST_CHECK(status);
	BOOST_CHECK(result.variable_comparison() == varcomp);
}
BOOST_AUTO_TEST_CASE(Test_substitute_varComp_MVRoot) {
}
BOOST_AUTO_TEST_CASE(Test_substitute_varComp_RAN) {
}

BOOST_AUTO_TEST_CASE(Test_getExplanation_degreeTooHigh) {
	carl::Variable x = carl::fresh_real_variable("x");
	carl::Variable y = carl::fresh_real_variable("y");
	std::vector<carl::Variable> ordering;
	ordering.push_back(x);
	ordering.push_back(y);

	ConstraintT c1(Poly(y)*y*y+Rational(1), carl::Relation::EQ);
	FormulaT f1(c1);
	std::vector<FormulaT> constraints;
	constraints.push_back(f1);

	Model varModel;
	varModel.emplace(x, Rational(0));

	mcsat::vs::ExplanationGenerator<mcsat::vs::DefaultSettings> generator(constraints, ordering, y, varModel);
	std::optional<mcsat::Explanation> result = generator.getExplanation();
	BOOST_CHECK(!result);	
}
BOOST_AUTO_TEST_CASE(Test_getExplanation_substitution) {
	carl::Variable x = carl::fresh_real_variable("x");
	carl::Variable y = carl::fresh_real_variable("y");
	std::vector<carl::Variable> ordering;
	ordering.push_back(x);
	ordering.push_back(y);

	std::vector<FormulaT> constraints;
	ConstraintT c1(carl::pow(Poly(x)-Rational(2),2) + carl::pow(Poly(y)-Rational(2),2) - Rational(1), carl::Relation::LESS);
	constraints.push_back(FormulaT(c1));
	ConstraintT c2(Poly(x)-y, carl::Relation::EQ);
	constraints.push_back(FormulaT(c2));

	Model varModel;
	varModel.emplace(x, Rational(0));

	mcsat::vs::ExplanationGenerator<mcsat::vs::DefaultSettings> generator(constraints, ordering, y, varModel);
	std::optional<mcsat::Explanation> result = generator.getExplanation();
	BOOST_CHECK(result);
	std::stringstream ss;
	ss << result.value();
	BOOST_CHECK(ss.str() == "(or (<= (+ (* (- 1) (* y y)) (* 4 y) (* (- 1) (* x x)) (* 4 x) (- 7)) 0) (!= (+ y (* (- 1) x)) 0) (< (+ (* 2 (* x x)) (* (- 8) x) 7) 0))");
}


BOOST_AUTO_TEST_SUITE_END();
