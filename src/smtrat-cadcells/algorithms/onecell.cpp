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
    SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got roots " << roots);
    if (roots.empty()) {
        tmp_sample.insert_or_assign(current_var, ran(0));
        if (!carl::evaluate(c, tmp_sample)) {
            results.emplace_back(datastructures::make_sampled_derivation<propset>(deriv,ran(0)));
            SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got interval " << results.back()->cell() << " wrt " << results.back()->delin());
            assert(results.back()->cell().lower_unbounded());
            assert(results.back()->cell().upper_unbounded());
        }
    } else {
        if (carl::isStrict(c.relation())) { // TODO later: allow weak bounds for sampled_derivations
            for (auto root = roots.begin(); root != roots.end(); root++) {
                results.emplace_back(datastructures::make_sampled_derivation(deriv, root->first));
                SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got interval " << results.back()->cell() << " wrt " << results.back()->delin());
                assert(results.back()->cell().is_section());
            }
        }
        // TODO unify neighbouring intervals whenever the poly does not change its sign at a zero

        {
            auto current_sample = ran(carl::sample_below(roots.begin()->first));
            tmp_sample.insert_or_assign(current_var, current_sample);
            if (c.relation() == carl::Relation::EQ || (c.relation() != carl::Relation::NEQ && !carl::evaluate(c, tmp_sample))) {
                results.emplace_back(datastructures::make_sampled_derivation(deriv, current_sample));
                SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got interval " << results.back()->cell() << " wrt " << results.back()->delin());
                assert(results.back()->cell().is_sector());
                assert(results.back()->cell().lower_unbounded());
            }
        }
        
        for (auto root = roots.begin(); root != std::prev(roots.end()); root++) {
            auto current_sample = carl::sample_between(root->first, std::next(root)->first);
            tmp_sample.insert_or_assign(current_var, current_sample);
            if (c.relation() == carl::Relation::EQ || (c.relation() != carl::Relation::NEQ && !carl::evaluate(c, tmp_sample))) {
                results.emplace_back(datastructures::make_sampled_derivation(deriv, current_sample));
                SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got interval " << results.back()->cell() << " wrt " << results.back()->delin());
                assert(results.back()->cell().is_sector());
                assert(!results.back()->cell().lower_unbounded());
                assert(!results.back()->cell().upper_unbounded());
            }
        }
        
        {
            auto current_sample = ran(carl::sample_above((--roots.end())->first));
            tmp_sample.insert_or_assign(current_var, current_sample);
            if (c.relation() == carl::Relation::EQ || (c.relation() != carl::Relation::NEQ && !carl::evaluate(c, tmp_sample))) {
                results.emplace_back(datastructures::make_sampled_derivation(deriv, current_sample));
                SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got interval " << results.back()->cell() << " wrt " << results.back()->delin());
                assert(results.back()->cell().is_sector());
                assert(results.back()->cell().upper_unbounded());
            }
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

    auto value_result = [&]() -> std::variant<std::pair<datastructures::indexed_root, ran>, datastructures::poly_ref> {
        if (std::holds_alternative<ran>(c.value())) {
            ran root = std::get<ran>(c.value());
            auto p = c.definingPolynomial();
            auto poly = proj.polys()(p);
            auto poly_roots = proj.real_roots(assignment(), poly);
            size_t index = std::distance(poly_roots.begin(), std::find(poly_roots.begin(), poly_roots.end(), root)) + 1;
            datastructures::indexed_root iroot(poly, index);
            return std::make_pair(iroot, root);
        } else {
            auto eval_res = std::get<MultivariateRootT>(c.value()).evaluate(sample);
            if (!eval_res) {
                auto p = c.definingPolynomial();
                return proj.polys()(p);
            } else {
                ran root = *eval_res;
                auto p = c.definingPolynomial();
                datastructures::indexed_root iroot(proj.polys()(p), std::get<MultivariateRootT>(c.value()).k());
                return std::make_pair(iroot, root);
            }
        }
    }();

    std::vector<datastructures::sampled_derivation_ref<propset>> results;

    if (std::holds_alternative<std::pair<datastructures::indexed_root, ran>>(value_result)) {
        datastructures::indexed_root& iroot = std::get<std::pair<datastructures::indexed_root, ran>>(value_result).first;
        ran& root = std::get<std::pair<datastructures::indexed_root, ran>>(value_result).second;

        deriv->insert(operators::properties::poly_pdel{ iroot.poly });
        deriv->insert(operators::properties::root_well_def{ iroot });
        deriv->delin().add_root(root, iroot);

        auto relation = c.negated() ? carl::inverse(c.relation()) : c.relation();
        bool point = relation == carl::Relation::GREATER || relation == carl::Relation::LESS || relation == carl::Relation::NEQ;
        bool below = relation == carl::Relation::GREATER || relation == carl::Relation::GEQ || relation == carl::Relation::EQ;
        bool above = relation == carl::Relation::LESS || relation == carl::Relation::LEQ || relation == carl::Relation::EQ;

        if (point) {
            results.emplace_back(datastructures::make_sampled_derivation(deriv, root));
            SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got interval " << results.back()->cell() << " wrt " << results.back()->delin());
        }
        if (below) {
            results.emplace_back(datastructures::make_sampled_derivation(deriv, ran(carl::sample_below(root))));
            SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got interval " << results.back()->cell() << " wrt " << results.back()->delin());
        }
        if (above) {
            results.emplace_back(datastructures::make_sampled_derivation(deriv, ran(carl::sample_above(root))));
            SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got interval " << results.back()->cell() << " wrt " << results.back()->delin());
        }
    } else {
        datastructures::poly_ref& poly = std::get<datastructures::poly_ref>(value_result);
        if (proj.is_nullified(sample, poly)) {
            deriv->delin().add_poly_nullified(poly);
        } else if (proj.num_roots(sample, poly) == 0) {
            deriv->insert(operators::properties::poly_pdel{ poly });
            deriv->delin().add_poly_noroot(poly);
        } else {
            assert(proj.num_roots(sample, poly) > 0 && proj.num_roots(sample, poly) < std::get<MultivariateRootT>(c.value()).k());
            deriv->insert(operators::properties::poly_pdel{ poly });
            deriv->insert(operators::properties::poly_sgn_inv{ deriv->proj().ldcf(poly) });
        }
        results.emplace_back(datastructures::make_sampled_derivation(deriv, ran(0)));
        SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got interval " << results.back()->cell() << " wrt " << results.back()->delin());
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
    SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got representation " << *covering_repr);

    SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Compute covering projection");
    auto cell_derivs = covering_repr->sampled_derivations();
    datastructures::merge_underlying(cell_derivs);
    operators::project_covering_properties<op>(*covering_repr);

    return covering_repr->cells.front().derivation.underlying().sampled_ref();
}

std::optional<std::pair<FormulasT, FormulaT>> onecell(const FormulasT& constraints, const variable_ordering& vars, const assignment& sample) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.algorithms.onecell", constraints << ", " << vars << ", " << sample);
    datastructures::poly_pool pool(vars);
    datastructures::projections proj(pool);

    auto cov_res = get_covering(proj, constraints, sample); // TODO later: alternative to covering: project delineation
    if (!cov_res) {
        return std::nullopt;
    }
    datastructures::sampled_derivation_ref<propset> cell_deriv = *cov_res;

    FormulasT description;
    while (cell_deriv->level() > 0) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Constructing cell on level " << cell_deriv->level());

        SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Project properties");
        operators::project_cell_properties<op>(*cell_deriv);
        operators::project_basic_properties<op>(*cell_deriv->base());
        SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Delineate properties");
        operators::delineate_properties<op>(*cell_deriv->delineated());
        cell_deriv->delineate_cell();
        SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got interval " << cell_deriv->cell() << " wrt " << cell_deriv->delin());
        SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Compute cell representation");
        auto cell_repr = representation::cell<representation::default_cell>::compute(cell_deriv);
        if (!cell_repr) {
            return std::nullopt;
        }
        SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got representation " << *cell_repr);
        SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Project cell");
        operators::project_delineated_cell_properties<op>(*cell_repr);

        description.emplace_back(helper::to_formula(proj.polys(), cell_deriv->main_var(),cell_repr->description));
        cell_deriv = cell_deriv->underlying().sampled_ref();
        proj.clear_cache(cell_deriv->level()+2);
    }

    return std::make_pair(constraints, FormulaT(carl::FormulaType::AND, std::move(description)));
}

}