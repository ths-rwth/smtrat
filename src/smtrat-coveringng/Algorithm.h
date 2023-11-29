#pragma once

#include "types.h"
#include "FormulaEvaluation.h"
#include "FormulaEvaluationNode.h"
#include "FormulaEvaluationGraph.h"
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

template<typename op>
inline std::optional<Interval<typename op::PropertiesSet>> get_enclosing_interval(cadcells::datastructures::Projections& proj, const boost::container::flat_set<cadcells::Constraint>& implicant, formula::Valuation root_valuation, const cadcells::Assignment& ass) {
    SMTRAT_LOG_FUNC("smtrat.covering_ng", implicant << ", " << root_valuation << ", " << ass);

    //std::size_t level = 0;
    //for (const auto& c : implicant) {
    //    level = std::max(carl::level_of(c.lhs()), level);
    //}
    //assert(level > 0 && level == ass.size());

    auto deriv = cadcells::datastructures::make_derivation<typename op::PropertiesSet>(proj, ass, ass.size()).sampled_ref();
    for (const auto& c : implicant) {
        if (carl::is_strict(c.relation())) {
            if (root_valuation == formula::Valuation::FALSE) {
                deriv->insert(cadcells::operators::properties::poly_semi_sgn_inv{ proj.polys()(c.lhs()) });
            } else {
                deriv->insert(cadcells::operators::properties::poly_sgn_inv{ proj.polys()(c.lhs()) });
            }
        } else {
            if (root_valuation == formula::Valuation::FALSE) {
                deriv->insert(cadcells::operators::properties::poly_sgn_inv{ proj.polys()(c.lhs()) });
            } else {
                deriv->insert(cadcells::operators::properties::poly_semi_sgn_inv{ proj.polys()(c.lhs()) });
            }
        }
    }
    if (!op::project_basic_properties(*deriv)) return std::nullopt;
    op::delineate_properties(*deriv);
    deriv->delineate_cell();
    SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got cell " << deriv->cell() << " w.r.t. delineation " << deriv->delin());
    return deriv;
}

template<typename FE, typename op>
inline std::vector<Interval<typename op::PropertiesSet>> get_enclosing_intervals(cadcells::datastructures::Projections& proj, const FE& f, const cadcells::Assignment& ass) {
    SMTRAT_LOG_FUNC("smtrat.covering_ng", "f, " << ass);
    auto implicants = f.compute_implicants();
    SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got implicants " << implicants);
    std::vector<Interval<typename op::PropertiesSet>> results;
    for (const auto& implicant : implicants) {
        auto interval = get_enclosing_interval<op>(proj, implicant, f.root_valuation(), ass);
        if (interval) results.emplace_back(*interval);
    }
    return results;
}

template<typename op, cadcells::representation::CoveringHeuristic covering_heuristic>
inline std::optional<Interval<typename op::PropertiesSet>> characterize_covering(const IntervalSet<typename op::PropertiesSet>& intervals) {
    SMTRAT_LOG_FUNC("smtrat.covering_ng", intervals);
    std::vector<Interval<typename op::PropertiesSet>> derivations(intervals.begin(), intervals.end());
    auto representation = cadcells::representation::covering<covering_heuristic>::compute(derivations);
    auto cell_derivs = representation.sampled_derivations();
    cadcells::datastructures::merge_underlying(cell_derivs);
    if (!op::project_covering_properties(representation)) return std::nullopt;
    Interval<typename op::PropertiesSet> new_deriv = cell_derivs.front()->underlying().sampled_ref();
    if (!op::project_basic_properties(*new_deriv)) return std::nullopt;
    op::delineate_properties(*new_deriv);
    new_deriv->delineate_cell();
    return new_deriv;
}

// TODO later: close cell if possible based on flag - implement here or in smtrat-cadcells?
// TODO later: optionally clear caches

template<typename FE, typename op, cadcells::representation::CoveringHeuristic covering_heuristic, smtrat::covering_ng::SamplingAlgorithm sampling_algorithm>
inline CoveringResult<typename op::PropertiesSet> exists(cadcells::datastructures::Projections& proj, FE& f, cadcells::Assignment ass) {
    SMTRAT_LOG_FUNC("smtrat.covering_ng", "f, " << ass);
    assert(f.root_valuation() != formula::Valuation::FALSE);
    IntervalSet<typename op::PropertiesSet> unsat_intervals;
    carl::Variable variable = first_unassigned_var(ass, proj.polys().var_order());
    std::optional<cadcells::RAN> sample;
    while(sample = sampling<sampling_algorithm>::template sample_outside<FE, typename op::PropertiesSet>(unsat_intervals, f), sample != std::nullopt) {
        SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got sample " << variable << " = " << sample);
        ass.emplace(variable, *sample);
        f.extend_valuation(ass);
        if (is_full_sample(ass, proj.polys().var_order()) && f.root_valuation() == formula::Valuation::MULTIVARIATE) {
            SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Got full sample, but formula does not evaluate");
            return CoveringResult<typename op::PropertiesSet>();
        }
        CoveringResult<typename op::PropertiesSet> res;
        if (f.root_valuation() == formula::Valuation::FALSE) {
            SMTRAT_LOG_TRACE("smtrat.covering_ng", "Formula evaluates to false");
            auto new_intervals = get_enclosing_intervals<FE, op>(proj, f, ass);
            if (new_intervals.size() > 0) res = CoveringResult<typename op::PropertiesSet>(new_intervals);
            else res = CoveringResult<typename op::PropertiesSet>(CoveringResult<typename op::PropertiesSet>::FAILED_PROJECTION);
        } else if (f.root_valuation() == formula::Valuation::TRUE) {
            SMTRAT_LOG_TRACE("smtrat.covering_ng", "Formula evaluates to true");
            res = CoveringResult<typename op::PropertiesSet>(ass);
        } else {
            SMTRAT_LOG_TRACE("smtrat.covering_ng", "Formula is multivariate");
            assert(!is_full_sample(ass, proj.polys().var_order()));
            res = exists<FE, op, covering_heuristic, sampling_algorithm>(proj, f, ass);
        }
        ass.erase(variable);
        f.revert_valuation(ass);
        if (res.is_failed()) {
            return CoveringResult<typename op::PropertiesSet>(res.status);
        } if (res.is_sat()) {
            return res.sample();
        } else {
            unsat_intervals.insert(res.intervals().begin(), res.intervals().end());
        }
    }
    if (ass.empty()) {
        return CoveringResult<typename op::PropertiesSet>(CoveringResult<typename op::PropertiesSet>::UNSAT);
    } else {
        auto new_interval = characterize_covering<op, covering_heuristic>(unsat_intervals);
        if (new_interval) {
            std::vector<Interval<typename op::PropertiesSet>> new_intervals({*new_interval});
            return CoveringResult<typename op::PropertiesSet>(new_intervals);
        }
        else {
            SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Failed due to incompleteness");
            return CoveringResult<typename op::PropertiesSet>(CoveringResult<typename op::PropertiesSet>::FAILED_PROJECTION);
        }
    }
}

}