#include <gtest/gtest.h>

#include <smtrat-common/logging.h>
#include <carl-logging/logging.h>
#include <carl-logging/logging-internals.h>

#include <smtrat-cadcells/common.h>
#include <smtrat-cadcells/helper_formula.h>
#include <smtrat-cadcells/operators/operator_mccallum.h>
#include <smtrat-cadcells/operators/operator_mccallum_filtered.h>
#include <smtrat-cadcells/representation/heuristics.h>
#include <smtrat-cadcells/algorithms/interval.h>

#include <carl-arith/ran/Conversion.h>
#include <carl-arith/poly/Conversion.h>
#include <carl-arith/constraint/Conversion.h>
#include <carl-arith/extended/Conversion.h>

using namespace smtrat::cadcells;

template<typename op, typename cell_heuristic>
std::optional<DNF> single_cell(const std::vector<Polynomial>& polys, Polynomial::ContextType context, const Assignment& sample) {
	datastructures::PolyPool pool(context);
    datastructures::Projections proj(pool);

	SMTRAT_STATISTICS_CALL(smtrat::cadcells::statistics().set_max_level(sample.size()+1));

	auto derivation = datastructures::make_derivation<typename op::PropertiesSet>(proj, sample, sample.size()).sampled_ref();
	for (const auto& p : polys) {
		derivation->insert(operators::properties::poly_sgn_inv{ pool(p) });
	}
	
    DNF description;
    while ((derivation)->level() > 0) {
        auto lvl = algorithms::get_interval<op, cell_heuristic>(derivation);
        SMTRAT_LOG_TRACE("smtrat.cadcells", "Polynomials: " << pool);
        if (!lvl) return std::nullopt;
        auto res = helper::to_formula(proj.polys(), lvl->first, lvl->second);
        description.insert(description.end(), res.begin(), res.end());
        proj.clear_assignment_cache((derivation)->sample());
        (derivation) = (derivation)->underlying().sampled_ref();
        proj.clear_cache((derivation)->level()+2);
    }
    proj.clear_assignment_cache(empty_assignment);

    return description;
}

auto as_carl(const DNF& cnf) {
	std::vector<smtrat::FormulaT> result;
	for (const auto& dis : cnf) {
		std::vector<smtrat::FormulaT> subresult;
		for (const auto& a : dis) {
			if (std::holds_alternative<Constraint>(a)) {
				subresult.emplace_back(smtrat::ConstraintT(carl::convert<smtrat::Poly>(std::get<Constraint>(a))));
			} else {
				auto vc = carl::convert<smtrat::Poly>(std::get<VariableComparison>(a));
				auto c = carl::as_constraint(vc);
				if (c) {
					subresult.emplace_back(smtrat::ConstraintT(*c));
				} else {
					subresult.emplace_back(vc);
				}
			}
		}
		result.emplace_back(carl::FormulaType::OR, std::move(subresult));
	}
	return smtrat::FormulaT(carl::FormulaType::AND, std::move(result));
}

struct McFSettings : operators::MccallumFilteredSettings {
	static constexpr auto delineation_function = ALL;
};

TEST(smtrat_cadcells, single_cell) {
	if (!carl::logging::logger().has("stdout")) {
		carl::logging::logger().configure("stdout", std::cout);
	}
	carl::logging::logger().filter("stdout")
	 	("smtrat.cadcells", carl::logging::LogLevel::LVL_TRACE)
	;

	using P = Polynomial;

	auto var_x = carl::fresh_real_variable("x");
	auto var_y = carl::fresh_real_variable("y");
	auto var_z = carl::fresh_real_variable("z");
	VariableOrdering vrs({ var_x, var_y, var_z });
	Polynomial::ContextType ctx(vrs);

	Assignment ass;
	ass.emplace(var_x,-1.25);
	ass.emplace(var_y,-0.5);
	ass.emplace(var_z,-2);

	auto poly_p = (P(ctx, var_y)*P(ctx, var_y)) + (P(ctx, var_z)*P(ctx, var_z)) - P(ctx, 1);
	auto poly_q = P(ctx, var_x) + P(ctx, var_y) + P(ctx, var_z);
	std::vector<P> polys({ poly_p, poly_q });

	std::cout << "--- DEFAULT ---" << std::endl;
	auto res_default = single_cell<operators::Mccallum<operators::MccallumSettings>, representation::cell_heuristics::LowestDegreeBarriers>(polys, ctx, ass);
	std::cout << res_default << std::endl;
	std::cout << as_carl(*res_default) << std::endl;
	std::cout << "--- FILTERED ---" << std::endl;
	auto res_filtered = single_cell<operators::MccallumFiltered<McFSettings>, representation::cell_heuristics::LowestDegreeBarriers>(polys, ctx, ass);
	std::cout << res_filtered << std::endl;
	std::cout << as_carl(*res_filtered) << std::endl;

	//ASSERT_EQ(res_default, res_filtered);
}
