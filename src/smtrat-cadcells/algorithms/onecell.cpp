#include "onecell.h"
#include "helper.h"

#include "../operators/operator_mccallum.h"
#include "../representation/heuristics.h"


namespace smtrat::cadcells::algorithms { // TODO write mcsat backend!

constexpr auto op = operators::op::mccallum;
using propset = operators::properties_set<op>::type;

std::vector<datastructures::sampled_derivation_ref<propset>> get_unsat_intervals(const ConstraintT& c, datastructures::projections& proj, const assignment& sample) {
    auto vars = proj.polys().var_order();
    auto current_var = vars[sample.size()];
    auto tmp_sample = sample;

    assert(level_of(vars, c.lhs()) == sample.size()+1);

    auto deriv = datastructures::make_derivation<propset>(proj, sample, sample.size() + 1);
    auto base_deriv = std::get<datastructures::base_derivation_ref<propset>>(deriv);

    base_deriv->insert(operators::properties::poly_sgn_inv{ proj.polys()(c.lhs()) });
    operators::project_basic_properties<op>(*base_deriv);
    operators::delineate_properties<op>(*base_deriv);

    std::vector<datastructures::sampled_derivation_ref<propset>> results;
    auto& roots = base_deriv->delin().roots(); 
    if (roots.empty()) {
        tmp_sample.emplace(current_var, ran(0));
        if (!carl::evaluate(c, tmp_sample)) {
            results.emplace_back(datastructures::make_sampled_derivation<propset>(base_deriv,ran(0)));
        }
    } else {
        results.emplace_back(datastructures::make_sampled_derivation(base_deriv, ran(carl::sample_below(roots.begin()->first))));
        for (auto root = roots.begin(); root != roots.end(); root++) {
            if (carl::isWeak(c.relation())) { // TODO later: allow weak bounds for sampled_derivations
                results.emplace_back(datastructures::make_sampled_derivation(base_deriv, root->first));
            }
            
            auto current_sample = carl::sample_between(root->first, std::next(root)->first);
            tmp_sample.emplace(current_var, current_sample);
            if (!carl::evaluate(c, tmp_sample)) {
                results.emplace_back(datastructures::make_sampled_derivation(base_deriv, current_sample));
            }
        }
        if (carl::isWeak(c.relation())) {
            results.emplace_back(datastructures::make_sampled_derivation(base_deriv, (--roots.end())->first));
        }
        auto current_sample = carl::sample_above((--roots.end())->first);
        tmp_sample.emplace(current_var, current_sample);
        if (!carl::evaluate(c, tmp_sample)) {
            results.emplace_back(datastructures::make_sampled_derivation(base_deriv, current_sample));
        }
    }
    return results;
}

/*
std::vector<datastructures::sampled_derivation_ref<propset>> get_unsat_intervals(const VariableComparisonT& c, datastructures::projections& proj, const assignment& sample) {
    auto vars = proj.polys().var_order();
    auto current_var = vars[sample.size()];
    auto tmp_sample = sample;

    assert(c.var() == current_var);
    assert(std::holds_alternative<ran>(c.value()) || level_of(vars, std::get<MultivariateRootT>(c.value()).poly(current_var) == sample.size() + 1));

    auto deriv = datastructures::make_derivation<propset>(proj, sample, sample.size() + 1);
    
    // TODO!!

    return;
}
*/

std::optional<datastructures::sampled_derivation_ref<propset>> get_covering(datastructures::projections& proj, const std::set<ConstraintT>& constraints, const assignment& sample) {
    std::vector<datastructures::sampled_derivation_ref<propset>> unsat_cells;
    for (const auto& c : constraints) {
        auto intervals = get_unsat_intervals(c, proj, sample);
        unsat_cells.insert(unsat_cells.end(), intervals.begin(), intervals.end());
    }

    auto covering_repr = representation::covering<representation::default_covering>::compute(unsat_cells); // TODO distinguish between: not enough interval for covering and mccallum fails
    if (!covering_repr) {
        return std::nullopt;
    }

    auto cell_derivs = covering_repr->sampled_derivations();
    datastructures::merge_underlying(cell_derivs);
    operators::project_covering_properties<op>(*covering_repr);

    return covering_repr->cells.front().derivation->base()->underlying_cell();
}

FormulaT onecell(const std::set<ConstraintT>& constraints, const variable_ordering& vars, const assignment& sample) {
    datastructures::poly_pool pool(vars);
    datastructures::projections proj(pool);

    auto cov_res = get_covering(proj, constraints, sample);
    if (!cov_res) {
        return FormulaT();
    }
    datastructures::sampled_derivation_ref<propset> cell_deriv = *cov_res;

    FormulasT description;
    while (cell_deriv->base()->level() > 0) {
        operators::project_cell_properties<op>(*cell_deriv);
        operators::project_basic_properties<op>(*cell_deriv->base());
        operators::delineate_properties<op>(*cell_deriv->base());
        cell_deriv->delineate_cell();
        auto cell_repr = representation::cell<representation::default_cell>::compute(cell_deriv);
        if (!cell_repr) {
            return FormulaT();
        }
        operators::project_delineated_cell_properties<op>(*cell_repr);

        description.emplace_back(helper::to_formula(proj.polys(), cell_deriv->base()->main_var(),cell_repr->description));
        if (cell_deriv->base()->level() > 1) cell_deriv = cell_deriv->base()->underlying_cell();
        else cell_deriv = nullptr;
        // TODO pool.clear(props->level()+1);
        // TODO proj.clear(props->level()+1);
    }

    return FormulaT(carl::FormulaType::AND, std::move(description));
}

}