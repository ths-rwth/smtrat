#include "onecell.h"
#include "helper.h"

#include "../operators/operator_mccallum.h"
#include "../representation/heuristics.h"


namespace smtrat::cadcells::algorithms {

constexpr auto op = operators::op::mccallum;
using propset = operators::properties_set<op>::type;

std::vector<datastructures::sampled_derivation_ref<propset>> get_unsat_intervals(const ConstraintT& c, datastructures::projections& proj, const assignment& sample) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.algorithms.onecell", c << ", " << sample);
    
    auto vars = proj.polys().var_order();
    auto current_var = vars[sample.size()];
    auto tmp_sample = sample;

    assert(cadcells::helper::level_of(vars, c.lhs()) == sample.size()+1);

    auto deriv = datastructures::make_derivation<propset>(proj, sample, sample.size() + 1).delineated_ref();

    deriv->insert(operators::properties::poly_sgn_inv{ proj.polys()(c.lhs()) });
    operators::project_basic_properties<op>(*deriv->base());
    operators::delineate_properties<op>(*deriv);

    std::vector<datastructures::sampled_derivation_ref<propset>> results;
    auto& roots = deriv->delin().roots(); 
    if (roots.empty()) {
        tmp_sample.emplace(current_var, ran(0));
        if (!carl::evaluate(c, tmp_sample)) {
            results.emplace_back(datastructures::make_sampled_derivation<propset>(deriv,ran(0)));
        }
    } else {
        results.emplace_back(datastructures::make_sampled_derivation(deriv, ran(carl::sample_below(roots.begin()->first))));
        for (auto root = roots.begin(); root != roots.end(); root++) {
            if (carl::isWeak(c.relation())) { // TODO later: allow weak bounds for sampled_derivations
                results.emplace_back(datastructures::make_sampled_derivation(deriv, root->first));
            }

            auto current_sample = carl::sample_between(root->first, std::next(root)->first);
            tmp_sample.emplace(current_var, current_sample);
            if (!carl::evaluate(c, tmp_sample)) {
                results.emplace_back(datastructures::make_sampled_derivation(deriv, current_sample));
            }
        }
        if (carl::isWeak(c.relation())) {
            results.emplace_back(datastructures::make_sampled_derivation(deriv, (--roots.end())->first));
        }
        auto current_sample = carl::sample_above((--roots.end())->first);
        tmp_sample.emplace(current_var, current_sample);
        if (!carl::evaluate(c, tmp_sample)) {
            results.emplace_back(datastructures::make_sampled_derivation(deriv, current_sample));
        }
    }
    return results;
}

std::vector<datastructures::sampled_derivation_ref<propset>> get_unsat_intervals(const VariableComparisonT& c, datastructures::projections& proj, const assignment& sample) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.algorithms.onecell", c << ", " << sample);

    auto vars = proj.polys().var_order();
    auto current_var = vars[sample.size()];
    auto tmp_sample = sample;

    assert(c.var() == current_var);
    assert(std::holds_alternative<ran>(c.value()) || cadcells::helper::level_of(vars, std::get<MultivariateRootT>(c.value()).poly(current_var)) == sample.size() + 1);

    auto deriv = datastructures::make_derivation<propset>(proj, sample, sample.size() + 1).delineated_ref();

    datastructures::indexed_root iroot;
    ran root;
    if (std::holds_alternative<ran>(c.value())) {
        root = std::get<ran>(c.value());
        auto poly = proj.polys()(c.definingPolynomial());
        auto poly_roots = proj.real_roots(assignment(), poly);
        size_t index = std::distance(poly_roots.begin(), std::find(poly_roots.begin(), poly_roots.end(), root)) + 1;
        iroot = datastructures::indexed_root(poly, index);
    } else {
        root = *std::get<MultivariateRootT>(c.value()).evaluate(sample);
        iroot = datastructures::indexed_root(proj.polys()(c.definingPolynomial()), std::get<MultivariateRootT>(c.value()).k());
    }

    deriv->insert(operators::properties::poly_pdel{ iroot.poly });
    deriv->insert(operators::properties::root_well_def{ iroot });
    deriv->delin().add_root(std::move(root), std::move(iroot));

    auto relation = c.negated() ? carl::inverse(c.relation()) : c.relation();
    bool point = relation == carl::Relation::GREATER || relation == carl::Relation::LESS || relation == carl::Relation::NEQ;
    bool below = relation == carl::Relation::GREATER || relation == carl::Relation::GEQ || relation == carl::Relation::EQ;
    bool above = relation == carl::Relation::LESS || relation == carl::Relation::LEQ || relation == carl::Relation::EQ;

    std::vector<datastructures::sampled_derivation_ref<propset>> results;
    if (point) {
        results.emplace_back(datastructures::make_sampled_derivation(deriv, root));
    }
    if (below) {
        results.emplace_back(datastructures::make_sampled_derivation(deriv, ran(carl::sample_below(root))));
    }
    if (above) {
        results.emplace_back(datastructures::make_sampled_derivation(deriv, ran(carl::sample_above(root))));
    }

    return results;
}

std::vector<datastructures::sampled_derivation_ref<propset>> get_unsat_intervals(const FormulaT& c, datastructures::projections& proj, const assignment& sample) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.algorithms.onecell", c << ", " << sample);
    if (c.getType() == carl::FormulaType::CONSTRAINT) {
        return get_unsat_intervals(c.constraint(), proj, sample);
    } else if (c.getType() == carl::FormulaType::VARCOMPARE) {
        return get_unsat_intervals(c.variableComparison(), proj, sample);
    } else {
        assert(false);
        return std::vector<datastructures::sampled_derivation_ref<propset>>();
    }
}

std::optional<datastructures::sampled_derivation_ref<propset>> get_covering(datastructures::projections& proj, const FormulasT& constraints, const assignment& sample) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.algorithms.onecell", constraints << ", " << sample);
    std::vector<datastructures::sampled_derivation_ref<propset>> unsat_cells;
    for (const auto& c : constraints) {
        auto intervals = get_unsat_intervals(c, proj, sample);
        unsat_cells.insert(unsat_cells.end(), intervals.begin(), intervals.end());
    }

    SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Computing covering representation");
    auto covering_repr = representation::covering<representation::default_covering>::compute(unsat_cells); // TODO distinguish between: not enough interval for covering and mccallum fails
    if (!covering_repr) {
        return std::nullopt;
    }

    SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Compute covering projection");
    auto cell_derivs = covering_repr->sampled_derivations();
    datastructures::merge_underlying(cell_derivs);
    operators::project_covering_properties<op>(*covering_repr);

    return covering_repr->cells.front().derivation.underlying().sampled_ref();
}

std::optional<FormulaT> onecell(const FormulasT& constraints, const variable_ordering& vars, const assignment& sample) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.algorithms.onecell", constraints << ", " << vars << ", " << sample);
    datastructures::poly_pool pool(vars);
    datastructures::projections proj(pool);

    auto cov_res = get_covering(proj, constraints, sample); // TODO later: alternative to covering: project delineation
    if (!cov_res) {
        return std::nullopt;
    }
    datastructures::sampled_derivation_ref<propset> cell_deriv = *cov_res;

    FormulasT description;
    while (cell_deriv->base()->level() > 0) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Constructing cell on level " << cell_deriv->base()->level());

        SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Project properties");
        operators::project_cell_properties<op>(*cell_deriv);
        operators::project_basic_properties<op>(*cell_deriv->base());
        SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Delineate properties");
        operators::delineate_properties<op>(*cell_deriv->delineated());
        cell_deriv->delineate_cell();
        SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Compute cell representation");
        auto cell_repr = representation::cell<representation::default_cell>::compute(cell_deriv);
        if (!cell_repr) {
            return std::nullopt;
        }
        SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Project cell");
        operators::project_delineated_cell_properties<op>(*cell_repr);

        description.emplace_back(helper::to_formula(proj.polys(), cell_deriv->main_var(),cell_repr->description));
        if (cell_deriv->base()->level() > 1) cell_deriv = cell_deriv->underlying().sampled_ref();
        else cell_deriv = nullptr;
        // TODO pool.clear(props->level()+1);
        // TODO proj.clear(props->level()+1);
    }

    return FormulaT(carl::FormulaType::AND, std::move(description));
}

}