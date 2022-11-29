#pragma once

#include <set>
#include <smtrat-cadcells/common.h>
#include <smtrat-cadcells/helper_formula.h>

#include <smtrat-cadcells/operators/operator_mccallum.h>
#include <smtrat-cadcells/operators/operator_mccallum_filtered.h>
#include <smtrat-cadcells/representation/heuristics.h>

#include <smtrat-cadcells/algorithms/level_covering.h>
#include <smtrat-cadcells/algorithms/interval.h>

#include <carl-formula/formula/functions/Visit.h>

namespace smtrat::mcsat::onecell {

struct LDBSettings {
    // constexpr static auto cell_heuristic = cadcells::representation::BIGGEST_CELL;
    // constexpr static auto cell_heuristic = cadcells::representation::CHAIN_EQ;
    // constexpr static auto cell_heuristic = cadcells::representation::LOWEST_DEGREE_BARRIERS_EQ;
    constexpr static auto cell_heuristic = cadcells::representation::LOWEST_DEGREE_BARRIERS;
    constexpr static auto covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING;
    // constexpr static auto covering_heuristic = cadcells::representation::CHAIN_COVERING;
    constexpr static auto op = cadcells::operators::op::mccallum;
};

struct LDBFilteredAllSelectiveSettings {
    constexpr static auto cell_heuristic = cadcells::representation::LOWEST_DEGREE_BARRIERS_EW;
    constexpr static auto covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING_EW;
    constexpr static auto op = cadcells::operators::op::mccallum_filtered_all_selective;
};

struct BCSettings {
    constexpr static auto cell_heuristic = cadcells::representation::BIGGEST_CELL;
    constexpr static auto covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING;
    constexpr static auto op = cadcells::operators::op::mccallum;
};

struct BCFilteredSettings {
    constexpr static auto cell_heuristic = cadcells::representation::BIGGEST_CELL_EW;
    constexpr static auto covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING_EW;
    constexpr static auto op = cadcells::operators::op::mccallum_filtered;
};

struct BCFilteredAllSettings : BCFilteredSettings{
    constexpr static auto op = cadcells::operators::op::mccallum_filtered_all;
};

struct BCFilteredBoundsSettings : BCFilteredSettings{
    constexpr static auto op = cadcells::operators::op::mccallum_filtered_bounds;
};

struct BCFilteredSamplesSettings : BCFilteredSettings{
    constexpr static auto op = cadcells::operators::op::mccallum_filtered_samples;
};

struct BCFilteredAllSelectiveSettings : BCFilteredSettings{
    constexpr static auto op = cadcells::operators::op::mccallum_filtered_all_selective;
};

constexpr static bool use_approximation = false;

struct BCApproximationSettings : BCSettings {
    constexpr static auto cell_apx_heuristic = cadcells::representation::BIGGEST_CELL_APPROXIMATION;
};

/**
 * An MCSAT-style single cell explanation function.
 * 
 * A set of constraints is called infeasible w.r.t. an assignment if the defining polynomials are univariate under the sample and there does not exists a value for the unassigned variable that satisfies all constraints.
 * 
 * This method eliminates the unassigned variable using @ref get_level_covering or @ref get_delineation and then constructs a single cell in the assigned variables level by level.
 * 
 * @param constraints Atoms of the same level such that @ref sample cannot be extended for the highest variable without making one atom false. Note that this property is not checked.
 * @param sample A sample such that all but the highest variable in @ref constraints are assigned.
 * @return A set of constraints whose conjunction describes an unsatisfying cell that can be concluded from the input constraints.
 */
template<typename Settings>
std::optional<std::vector<cadcells::Atom>> onecell(const std::vector<cadcells::Atom>& constraints, const cadcells::Polynomial::ContextType& context, const cadcells::Assignment& sample) {
    #ifdef SMTRAT_DEVOPTION_Statistics
        cadcells::OCApproximationStatistics& stats = cadcells::OCApproximationStatistics::get_instance();
        stats.newCell();
    #endif

    bool consider_approximation = use_approximation && cadcells::representation::approximation::ApxCriteria::cell(constraints);
    #ifdef SMTRAT_DEVOPTION_Statistics
        if (consider_approximation) stats.approximationConsidered();
    #endif
    
    SMTRAT_LOG_FUNC("smtrat.mcsat.onecell", constraints << ", " << context << ", " << sample);
    cadcells::datastructures::PolyPool pool(context);
    cadcells::datastructures::Projections proj(pool);

    // if all input constraints are "strict" (their unsat cells can be closed), then we can close the cell, i.e. make the bounds weak
    bool constraints_all_strict = std::find_if(constraints.begin(), constraints.end(), [&](const auto& f) {
        if (std::holds_alternative<cadcells::Constraint>(f)) return !carl::is_strict(std::get<cadcells::Constraint>(f).relation());
        else if (std::holds_alternative<cadcells::VariableComparison>(f)) {
            auto vc = std::get<cadcells::VariableComparison>(f);
            // Negated VariableComparisons evaluate to true where its MultivariateRoot is undefined. Thus, their unsatisfying region is never closed! 
            if (vc.negated()) return true;
            if (!carl::is_strict(vc.relation())) return true;
            // If the VariableComparison is not well-defined at the given sample, then the unsatusfying region is not closed, as it might get well-defined at the boundary.
            auto mv = std::get<carl::MultivariateRoot<cadcells::Polynomial>>(vc.value());
            auto mvp = pool(mv.poly());
            if (proj.is_nullified(sample, mvp) || proj.real_roots(sample, mvp).size() < mv.k()) return true;
            return false;
        }
        assert(false);
        return false;
    }) == constraints.end();
    SMTRAT_LOG_TRACE("smtrat.mcsat.onecell", "constraints_all_strict = " << constraints_all_strict);

    auto derivation = cadcells::algorithms::get_level_covering<Settings::op, Settings::covering_heuristic>(proj, constraints, sample);
    SMTRAT_LOG_TRACE("smtrat.mcsat.onecell", "Polynomials: " << pool);
    if (!derivation) {
        return std::nullopt;
    }

    std::vector<cadcells::Atom> description;
    while ((*derivation)->level() > 0) {
        std::optional<std::pair<carl::Variable, cadcells::datastructures::SymbolicInterval>> lvl;
        if constexpr (use_approximation) {
            if (consider_approximation && cadcells::representation::approximation::ApxCriteria::level((*derivation)->level())) {
                lvl = cadcells::algorithms::get_interval<Settings::op, Settings::cell_apx_heuristic>(*derivation);
            } else {
                lvl = cadcells::algorithms::get_interval<Settings::op, Settings::cell_heuristic>(*derivation);
            }
        } else {
            lvl = cadcells::algorithms::get_interval<Settings::op, Settings::cell_heuristic>(*derivation);
        }
        SMTRAT_LOG_TRACE("smtrat.mcsat.onecell", "Polynomials: " << pool);
        if (!lvl) {
            return std::nullopt;
        }
        if (constraints_all_strict) {
            lvl->second.set_to_closure();
        }
        auto res = cadcells::helper::to_formula(proj.polys(), lvl->first, lvl->second);
        description.insert(description.end(), res.begin(), res.end());
        proj.clear_assignment_cache((*derivation)->sample());
        (*derivation) = (*derivation)->underlying().sampled_ref();
        proj.clear_cache((*derivation)->level()+2);
    }
    proj.clear_assignment_cache(cadcells::empty_assignment);

    return description;
}

}
