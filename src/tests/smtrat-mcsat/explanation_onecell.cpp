#include <gtest/gtest.h>

#include <smtrat-common/logging.h>
#include <carl-logging/logging.h>
#include <carl-logging/logging-internals.h>
#include <smtrat-mcsat/explanations/onecell/onecell.h>

TEST(smtrat_mcsat, onecell)
{
	if (!carl::logging::logger().has("stdout")) {
		carl::logging::logger().configure("stdout", std::cout);
	}
	carl::logging::logger().filter("stdout")
	 	("smtrat.cadcells", carl::logging::LogLevel::LVL_TRACE)
	 	("smtrat.mcsat.onecell", carl::logging::LogLevel::LVL_TRACE)
	;

	using P = smtrat::cadcells::Polynomial;

	auto var_s = carl::fresh_real_variable("s");
	auto var_p = carl::fresh_real_variable("p");
	auto var_d = carl::fresh_real_variable("d");
	auto var_b = carl::fresh_real_variable("b");
	smtrat::cadcells::VariableOrdering vrs({ var_s, var_p, var_d, var_b });
	smtrat::cadcells::Polynomial::ContextType ctx(vrs);

	smtrat::cadcells::Assignment ass;
	ass.emplace(var_s,0);
	ass.emplace(var_p,0);
	ass.emplace(var_d,0);

	auto poly_p = P(ctx, var_b) - P(ctx, 1);
	auto poly_q = P(ctx, var_b) + P(ctx, var_s) + (P(ctx, var_d) * P(ctx, var_p));

	auto constr_p = smtrat::cadcells::Constraint(poly_p, carl::Relation::EQ);
	auto constr_q = smtrat::cadcells::Constraint(poly_q, carl::Relation::EQ);
	std::vector<smtrat::cadcells::Atom> constrs;
	constrs.emplace_back(constr_p);
	constrs.emplace_back(constr_q);

	std::cout << "--- DEFAULT ---" << std::endl;
	auto res_default = smtrat::mcsat::onecell::onecell<smtrat::mcsat::onecell::DefaultSettings>(constrs, ctx, ass);
	std::cout << res_default << std::endl;
	std::cout << "--- FILTERED ---" << std::endl;
	auto res_filtered = smtrat::mcsat::onecell::onecell<smtrat::mcsat::onecell::FilteredSettings>(constrs, ctx, ass);
	std::cout << res_filtered << std::endl;

	ASSERT_EQ(res_default, res_filtered);
}
