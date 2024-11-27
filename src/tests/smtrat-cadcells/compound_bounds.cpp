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

template<typename op>
auto set_up(datastructures::Projections& proj, const std::vector<Polynomial>& polys, const Assignment& sample) {
	SMTRAT_STATISTICS_CALL(smtrat::cadcells::statistics().set_max_level(sample.size()+1));
	auto derivation = datastructures::make_derivation<typename op::PropertiesSet>(proj, sample, sample.size()).sampled_ref();
	for (const auto& p : polys) {
		derivation->insert(operators::properties::poly_sgn_inv{ proj.polys()(p) });
	}
	return derivation;
}

template<typename op>
auto get_interval_using(datastructures::SampledDerivationRef<typename op::PropertiesSet>& cell_deriv, datastructures::CellRepresentation<typename op::PropertiesSet>& cell_repr) {
    assert((cell_deriv)->level() > 0);
	SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Constructing cell on level " << cell_deriv->level());
    SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Project properties");
    if (!op::project_basic_properties(*cell_deriv)) return DNF();
    SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Delineate properties");
    op::delineate_properties(*cell_deriv);
    cell_deriv->delineate_cell();
    SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got interval " << cell_deriv->cell() << " wrt " << cell_deriv->delin());
    SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Compute cell representation");
    SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got representation " << cell_repr);
    if (cell_deriv->level() > 1) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Project cell");
        if (!op::project_cell_properties(cell_repr)) return DNF();
    }
	return helper::to_formula(cell_deriv->polys(), cell_deriv->main_var(), cell_repr.description);
}

template<typename op>
auto next_level(datastructures::SampledDerivationRef<typename op::PropertiesSet> deriv) {
	SMTRAT_LOG_TRACE("smtrat.cadcells", "Polynomials: " << deriv->polys());
	return deriv->underlying().sampled_ref();
}

auto as_carl(const std::vector<Atom>& atoms) {
	std::vector<smtrat::FormulaT> result;
	for (const auto& a : atoms) {
		if (std::holds_alternative<Constraint>(a)) {
			result.emplace_back(smtrat::ConstraintT(carl::convert<smtrat::Poly>(std::get<Constraint>(a))));
		} else {
			auto vc = carl::convert<smtrat::Poly>(std::get<VariableComparison>(a));
			auto c = carl::as_constraint(vc);
			if (c) {
				result.emplace_back(smtrat::ConstraintT(*c));
			} else {
				result.emplace_back(vc);
			}
		}
	}
	return result;
}

struct McFSettings : operators::MccallumFilteredSettings {
	static constexpr auto delineation_function = COMPOUND;
};

TEST(smtrat_cadcells, compound_bounds) {
	if (!carl::logging::logger().has("stdout")) {
		carl::logging::logger().configure("stdout", std::cout);
	}
	carl::logging::logger().filter("stdout")
	 	("smtrat.cadcells", carl::logging::LogLevel::LVL_TRACE)
	;

	using P = Polynomial;

	// auto var_x = carl::fresh_real_variable("x");
	auto var_y = carl::fresh_real_variable("x"); // y
	auto var_z = carl::fresh_real_variable("y"); // z
	VariableOrdering vrs({ var_y, var_z });
	// VariableOrdering vrs({ var_x, var_y, var_z });
	Polynomial::ContextType ctx(vrs);

	Assignment ass;
	// ass.emplace(var_x,-1.25);
	ass.emplace(var_y,0.1);
	ass.emplace(var_z,0);

	auto poly_p = (P(ctx, var_y)*P(ctx, var_y)) + (P(ctx, var_z)*P(ctx, var_z)) - P(ctx, 1);
	auto poly_q = P(ctx, 4)*P(ctx, var_z) - P(ctx, 5);
	std::vector<P> polys({ poly_p, poly_q });

	datastructures::PolyPool pool(ctx);
    datastructures::Projections proj(pool);
	auto deriv = set_up<operators::MccallumFiltered<McFSettings>>(proj, polys, ass);

	auto upper_1 = P(ctx, 4)*P(ctx, var_y) + P(ctx, 4)*P(ctx, var_z) - P(ctx, 3);
	auto upper_2 = P(ctx, 4)*P(ctx, var_y) - P(ctx, 4)*P(ctx, var_z) + P(ctx, 3);
	datastructures::CompoundMinMax ub_minmax;
	ub_minmax.roots.emplace_back();
	ub_minmax.roots.back().emplace_back(deriv->polys()(upper_1), 1);
	ub_minmax.roots.emplace_back(); 
	ub_minmax.roots.back().emplace_back(deriv->polys()(upper_2), 1);
	datastructures::RootFunction upper_bound(std::move(ub_minmax));
	datastructures::CellRepresentation repr_z(deriv);
	repr_z.description = datastructures::SymbolicInterval(datastructures::Bound::strict(datastructures::RootFunction(datastructures::IndexedRoot(deriv->polys()(poly_p), 1))), datastructures::Bound::strict(upper_bound));
	repr_z.ordering.add_less(datastructures::IndexedRoot(deriv->polys()(poly_p), 1), upper_bound);
	repr_z.ordering.add_less(upper_bound, datastructures::IndexedRoot(deriv->polys()(poly_p), 2));
	repr_z.ordering.add_less(upper_bound, datastructures::IndexedRoot(deriv->polys()(poly_q), 1));
	auto res_z = get_interval_using<operators::MccallumFiltered<McFSettings>>(deriv, repr_z);
	deriv = next_level<operators::MccallumFiltered<McFSettings>>(deriv);
	std::cout << res_z << std::endl;
	ASSERT_FALSE(res_z.empty());

	auto res_y = algorithms::get_interval<operators::MccallumFiltered<McFSettings>, typename representation::cell_heuristics::BiggestCellFilter>(deriv);
	deriv = next_level<operators::MccallumFiltered<McFSettings>>(deriv);
	std::cout << res_y << std::endl;
	
	//ASSERT_EQ(res_default, res_filtered);
}
