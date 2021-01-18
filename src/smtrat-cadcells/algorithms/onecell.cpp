#include "onecell.h"
#include "helper.h"

#include "../operators/operator_mccallum.h"


namespace smtrat::cadcells::algorithms { // TODO write mcsat backend!

std::vector<std::shared_ptr<sampled_derivation>> get_unsat_intervals(const ConstraintT& c, const projection& proj, const assignment& sample) {
    auto vars = proj.polys().var_order();
    auto current_var = vars[sample.size()];
    auto tmp_sample = sample;

    assert(level_of(vars, c.lhs()) == sample.size()+1);

    auto deriv = make_derivation<properties<op::mccallum>>(proj, sample, sample.size() + 1);

    deriv->insert(operators::properties::sgn_inv(pool(c.lhs())));
    operators::project_basic_properties<op::mccallum>(deriv);
    operators::delineate_cell_properties<op::mccallum>(deriv);

    std::vector<std::shared_ptr<sampled_derivation>> results;
    auto& roots = deriv.delin().roots(); 
    if (roots.empty()) {
        tmp_sample.insert(current_var, 0);
        if (!carl::evaluate(c, tmp_sample)) {
            results.emplace_back(make_sampled_derivation(deriv,0));
        }
    } else {
        results.emplace_back(deriv.delineate_cell(carl::sample_below(roots.front().first)));        
        for (auto root = roots.begin(); root != roots.end(); root++) {
            if (c.relation().isWeak()) { // TODO later: allow weak bounds for sampled_derivations
                results.emplace_back(make_sampled_derivation(deriv, root->first));
            }
            
            auto current_sample = carl::sample_between(root->first, (root+1)->first);
            tmp_sample.insert(current_var, 0);
            if (!carl::evaluate(c, tmp_sample)) {
                results.emplace_back(make_sampled_derivation(deriv, current_sample));
            }
        }
        if (c.relation().isWeak()) {
            results.emplace_back(make_sampled_derivation(deriv, roots.back().first));
        }
        auto current_sample = carl::sample_above(roots.back().first);
        tmp_sample.insert(current_var, 0);
        if (!carl::evaluate(c, tmp_sample)) {
            results.emplace_back(make_sampled_derivation(deriv, current_sample));
        }
    }
    return results;
}

std::vector<std::shared_ptr<sampled_derivation>> get_unsat_intervals(const VariableComparisonT& c, const projection& proj, const assignment& sample) {
    auto vars = proj.polys().var_order();
    auto current_var = vars[sample.size()];
    auto tmp_sample = sample;

    assert(c.var() == current_var);
    assert(std::holds_alternative<ran>(c.value()) || level_of(vars, std::get<MultivariateRootT>(c.value()).poly(current_var) == sample.size() + 1));

    auto deriv = make_derivation<properties<op::mccallum>>(proj, sample, sample.size() + 1);
    
    // TODO!!

    return;
}

std::optional<sampled_derivation_ref> covering(datastructures::projections& proj, const std::set<ConstraintT>& constraints, const assignment& sample) {
    std::vector<sampled_derivation_ref> unsat_cells;
    for (const auto& c : constraints) {
        unsat_cells.push_back(get_unsat_intervals(c, proj, sample));
    }

    auto covering_representation = compute_representation(unsat_cells); // TODO distinguish between: not enough interval for covering and mccallum fails
    if (!covering_representation) {
        return std::nullopt;
    }

    merge_underlying_cells(covering_representation.sampled_derivations());
    project_covering_properties<op::mccallum>(covering_representation);

    return covering_representation.cells.first().underlying_cell();
}

FormulaT onecell(const std::set<ConstraintT>& constraints, const variable_ordering& vars, const assignment& sample) {
    datastructures::poly_pool pool(vars);
    datastructures::projections proj(pool);

    auto cov_res = covering(proj, constraints, sample);
    if (!cov_res) {
        return FormulaT();
    }
    sampled_derivation_ref cell_deriv = *cov_res;

    FormulasT description;
    while (props->level() > 0) {
        operators::project_cell_properties(*cell_deriv);
        operators::project_basic_properties(*cell_deriv);
        operators::delineate_properties(*cell_deriv);
        cell_deriv.delineate_cell();
        auto cell_representation = compute_representation(*cell_deriv);
        if (!cell_representation) {
            return FormulaT();
        }
        operators::project_delineated_cell_properties(cell_representation);

        description.emplace_back(helper::to_formula(cell_deriv.main_var(),cell_representation.cell));
        if (props->level() > 1) cell_deriv = cell_deriv->underlying_cell();
        else cell_deriv = std::nullptr;
        pool.clear(props->level()+1);
        proj.clear(props->level()+1);
    }

    return FormulaT(carl::FormulaType::AND, std::move(description));
}

}