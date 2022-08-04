#include <gtest/gtest.h>

#include <smtrat-cadcells/datastructures/polynomials.h>

TEST(smtrat_cadcells, datastructures_polynomials)
{
	smtrat::cadcells::VariableOrdering vrs;
	smtrat::cadcells::Polynomial::ContextType ctx(vrs);
	smtrat::cadcells::Polynomial poly(ctx, 1);
	smtrat::cadcells::datastructures::PolyPool pool(ctx);
	ASSERT_EQ(pool(pool(poly)), poly);
}
