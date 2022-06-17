#pragma once

#include <set>
#include <smtrat-cadcells/common.h>
#include <smtrat-cadcells/helper_formula.h>

#include <smtrat-cadcells/operators/operator_mccallum.h>
#include <smtrat-cadcells/representation/heuristics.h>

#include <smtrat-cadcells/algorithms/level_covering.h>
#include <smtrat-cadcells/algorithms/delineation.h>
#include <smtrat-cadcells/algorithms/interval.h>

#include <carl-formula/formula/functions/Visit.h>

namespace smtrat::mcsat::onecell {

// constexpr auto cell_heuristic = cadcells::representation::BIGGEST_CELL;
// constexpr auto cell_heuristic = cadcells::representation::CHAIN_EQ;
// constexpr auto cell_heuristic = cadcells::representation::LOWEST_DEGREE_BARRIERS_EQ;
constexpr auto cell_heuristic = cadcells::representation::LOWEST_DEGREE_BARRIERS;
constexpr auto covering_heuristic = cadcells::representation::DEFAULT_COVERING;
// constexpr auto covering_heuristic = cadcells::representation::CHAIN_COVERING;
constexpr auto op = cadcells::operators::op::mccallum;
constexpr bool use_delineation = false; 

/**
 * An MCAST-style single cell explanation function.
 * 
 * A set of constraints is called infeasible w.r.t. an assignment if the defining polynomials are univariate under the sample and there does not exists a value for the unassigned variable that satisfies all constraints.
 * 
 * This method eliminates the unassigned variable using @ref get_level_covering or @ref get_delineation and then constructs a single cell in the assigned variables level by level.
 * 
 * @param constraints Atoms of the same level such that @ref sample cannot be extended for the highest variable without making one atom false. Note that this property is not checked.
 * @param sample A sample such that all but the highest variable in @ref constraints are assigned.
 * @return A pair of a set of constraints causign the conflict and a formula describing the cell.
 */
std::optional<std::pair<FormulasT, FormulaT>> onecell(const FormulasT& constraints, const cadcells::VariableOrdering& vars, const cadcells::Assignment& sample) {
    SMTRAT_LOG_FUNC("smtrat.mcsat.onecell", constraints << ", " << vars << ", " << sample);
    cadcells::datastructures::PolyPool pool(vars);
    cadcells::datastructures::Projections proj(pool);

    // if all input constraints are strict, then we can close the cell, i.e. make the bounds weak
    bool constraints_all_strict = std::find_if(constraints.begin(), constraints.end(), [](const auto& f) {
        if (f.type()==carl::FormulaType::CONSTRAINT) return !carl::is_strict(f.constraint().relation());
        else if (f.type()==carl::FormulaType::VARCOMPARE) return (!carl::is_strict(f.variable_comparison().relation()) && !f.variable_comparison().negated()) || (carl::is_strict(f.variable_comparison().relation()) && f.variable_comparison().negated());
        assert(false);
        return false;
    }) == constraints.end();
    SMTRAT_LOG_TRACE("smtrat.mcsat.onecell", "constraints_all_strict = " << constraints_all_strict);

    std::optional<cadcells::datastructures::SampledDerivationRef<typename cadcells::operators::PropertiesSet<op>::type>> derivation;
    if (use_delineation) {
        derivation = cadcells::algorithms::get_delineation<op, cadcells::representation::CHAIN>(proj, constraints, sample);
    } else {
        derivation = cadcells::algorithms::get_level_covering<op, covering_heuristic>(proj, constraints, sample);
    }
    if (!derivation) {
        return std::nullopt;
    }

    FormulasT description;
    while ((*derivation)->level() > 0) {
        auto lvl = cadcells::algorithms::get_interval<op, cell_heuristic>(*derivation);
        if (!lvl) {
            return std::nullopt;
        }
        if (constraints_all_strict) {
            lvl->second.set_to_closure();
        }
        description.emplace_back(cadcells::helper::to_formula(proj.polys(), lvl->first, lvl->second));
        proj.clear_assignment_cache((*derivation)->sample());
        (*derivation) = (*derivation)->underlying().sampled_ref();
        proj.clear_cache((*derivation)->level()+2);
    }
    proj.clear_assignment_cache(cadcells::empty_assignment);

    return std::make_pair(constraints, FormulaT(carl::FormulaType::AND, std::move(description)));
}

}
