#include <gtest/gtest.h>

#include <smtrat-cadcells/datastructures/polynomials.h>

TEST(smtrat_cadcells, datastructures_polynomials)
{
	smtrat::Poly poly(2);
	smtrat::cadcells::datastructures::PolyPool pool({});
	ASSERT_EQ(pool(pool(poly)), smtrat::Poly(1));
}
