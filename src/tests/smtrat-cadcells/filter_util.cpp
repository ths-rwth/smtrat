#include <gtest/gtest.h>

#include <smtrat-cadcells/datastructures/derivation.h>
#include <smtrat-cadcells/operators/properties.h>
#include <smtrat-cadcells/operators/rules.h>
#include <smtrat-cadcells/operators/rules_filter_util.h>

TEST(smtrat_cadcells, filter_util_has_intersection)
{
    using Rational=mpq_class;
    auto x = carl::fresh_real_variable("x");
	carl::LPRealAlgebraicNumber ran1(carl::UnivariatePolynomial<Rational>(x,{Rational(-1),Rational(0),Rational(81)}), carl::Interval<Rational>(Rational(0),Rational(1)/4));
    carl::LPRealAlgebraicNumber ran2(carl::UnivariatePolynomial<Rational>(x,{Rational(-1),Rational(9)}), carl::Interval<Rational>(Rational(0),Rational(1)/4));

    std::cout << ran1 << " " << ran2 << std::endl;

    // has_intersection(<81*x^2 + (-1), (0, 1/4)>, <9*x + (-1), (0, 1/4)>)

	ASSERT_TRUE(smtrat::cadcells::operators::rules::filter_util::has_intersection(ran1,ran2));
}
