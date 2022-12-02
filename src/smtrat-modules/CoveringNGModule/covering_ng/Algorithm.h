#pragma once

#include "types.h"
#include "FormulaEvaluation.h"
#include "Sampling.h"

namespace smtrat::covering_ng {

inline carl::Variable first_unassigned_var(const cadcells::Assignment& ass, const cadcells::VariableOrdering& var_order) {
    for (const auto& var : var_order) {
        if (ass.find(var) == ass.end()) return var;
    }
    assert(false);
    return carl::Variable();
}

inline bool is_full_sample(const cadcells::Assignment& ass, const cadcells::VariableOrdering& var_order) {
    for (const auto& var : var_order) {
        if (ass.find(var) == ass.end()) return false;
    }
    return true;
}

template<cadcells::operators::op op>
inline std::optional<Interval<op>> get_enclosing_interval(cadcells::datastructures::Projections& proj, const formula::FormulaEvaluation& f, const cadcells::Assignment& ass) {
    SMTRAT_LOG_FUNC("smtrat.covering_ng", "f, " << ass);
    boost::container::flat_set<cadcells::Constraint> implicant;
    formula::compute_implicant(f, implicant);
    SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got implicant " << implicant);

    std::size_t level = 0;
    for (const auto& c : implicant) {
        level = carl::level_of(c.lhs()) > level ? carl::level_of(c.lhs()) : level;
    }
    assert(level > 0 && level == ass.size());

    auto deriv = cadcells::datastructures::make_derivation<typename cadcells::operators::PropertiesSet<op>::type>(proj, ass, ass.size()).sampled_ref();
    for (const auto& c : implicant) {
        if (carl::is_strict(c.relation())) {
            if (f.c().valuation == formula::Valuation::FALSE) {
                deriv->insert(cadcells::operators::properties::poly_semi_sgn_inv{ proj.polys()(c.lhs()) });
            } else {
                deriv->insert(cadcells::operators::properties::poly_sgn_inv{ proj.polys()(c.lhs()) });
            }
        } else {
            if (f.c().valuation == formula::Valuation::FALSE) {
                deriv->insert(cadcells::operators::properties::poly_sgn_inv{ proj.polys()(c.lhs()) });
            } else {
                deriv->insert(cadcells::operators::properties::poly_semi_sgn_inv{ proj.polys()(c.lhs()) });
            }
        }
    }
    if (!cadcells::operators::project_basic_properties<op>(*deriv->delineated())) return std::nullopt;
    cadcells::operators::delineate_properties<op>(*deriv);
    deriv->delineate_cell();
    SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got cell " << deriv->cell() << " w.r.t. delineation " << deriv->delin());
    return deriv;
}

template<cadcells::operators::op op, cadcells::representation::CoveringHeuristic covering_heuristic>
inline std::optional<Interval<op>> characterize_covering(const IntervalSet<op>& intervals) {
    SMTRAT_LOG_FUNC("smtrat.covering_ng", intervals);
    std::vector<Interval<op>> derivations(intervals.begin(), intervals.end());
    auto representation = cadcells::representation::covering<covering_heuristic>::compute(derivations);
    if (!representation) return std::nullopt;
    auto cell_derivs = representation->sampled_derivations();
    cadcells::datastructures::merge_underlying(cell_derivs);
    cadcells::operators::project_covering_properties<op>(*representation);
    Interval<op> new_deriv = cell_derivs.front()->underlying().sampled_ref();
    if (!cadcells::operators::project_cell_properties<op>(*new_deriv)) return std::nullopt;
    cadcells::operators::project_basic_properties<op>(*new_deriv->delineated());
    cadcells::operators::delineate_properties<op>(*new_deriv);
    new_deriv->delineate_cell();
    return new_deriv;
}

// TODO later: close cell if possible based on flag - implement here or in smtrat-cadcells?
// TODO later: sampling also based on formula
// TODO later: do Boolean propagation while solving
// TODO later: optionally clear caches

template<cadcells::operators::op op, cadcells::representation::CoveringHeuristic covering_heuristic, smtrat::covering_ng::SamplingAlgorithm sampling_algorithm>
inline CoveringResult<op> exists(cadcells::datastructures::Projections& proj, formula::FormulaEvaluation& f, cadcells::Assignment ass) {
    SMTRAT_LOG_FUNC("smtrat.covering_ng", "f, " << ass);
    assert(f.c().valuation != formula::Valuation::FALSE);
    IntervalSet<op> unsat_intervals;
    carl::Variable variable = first_unassigned_var(ass, proj.polys().var_order());
    std::optional<cadcells::RAN> sample;
    while(sample = sampling<sampling_algorithm>::template sample_outside<op>(unsat_intervals, f), sample != std::nullopt) {
        SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got sample " << variable << " = " << sample);
        ass.emplace(variable, *sample);
        formula::extend_valuation(f, ass);
        if (is_full_sample(ass, proj.polys().var_order()) && f.c().valuation == formula::Valuation::MULTIVARIATE) {
            SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Got full sample, but formula does not evaluate");
            return CoveringResult<op>();
        }
        CoveringResult<op> res;
        if (f.c().valuation == formula::Valuation::FALSE) {
            SMTRAT_LOG_TRACE("smtrat.covering_ng", "Formula evaluates to false");
            auto new_interval = get_enclosing_interval<op>(proj, f, ass);
            if (new_interval) res = CoveringResult<op>(*new_interval);
            else res = CoveringResult<op>(CoveringResult<op>::FAILED_PROJECTION);
        } else if (f.c().valuation == formula::Valuation::TRUE) {
            SMTRAT_LOG_TRACE("smtrat.covering_ng", "Formula evaluates to true");
            res = CoveringResult<op>(ass);
        } else {
            SMTRAT_LOG_TRACE("smtrat.covering_ng", "Formula is multivariate");
            assert(!is_full_sample(ass, proj.polys().var_order()));
            res = exists<op, covering_heuristic, sampling_algorithm>(proj, f, ass);
        }
        ass.erase(variable);
        formula::revert_valuation(f, ass.size());
        if (res.is_failed()) {
            return CoveringResult<op>(res.status);
        } if (res.is_sat()) {
            return res.sample();
        } else {
            unsat_intervals.insert(res.interval());
        }
    }
    if (ass.empty()) {
        return CoveringResult<op>(CoveringResult<op>::UNSAT);
    } else {
        auto new_interval = characterize_covering<op, covering_heuristic>(unsat_intervals);
        if (new_interval) return CoveringResult<op>(*new_interval);
        else {
            SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Failed due to incompleteness");
            return CoveringResult<op>(CoveringResult<op>::FAILED_PROJECTION);
        }
    }
}

}