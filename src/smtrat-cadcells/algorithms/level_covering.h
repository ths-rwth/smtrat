#include "unsat_intervals.h"

namespace smtrat::cadcells::algorithms {

/**
 * Computes an unsat covering w.r.t. a set of constraints.
 * 
 * If a constraint is univariate under a sample, for the unassinged variables, the constraint induces intervals in which the constraint will be conflicting. If multiple such intervals from a set of constraints cover the real line, then the partial sample cannot be extended without making a conflict. This conflict is generalized.
 * 
 * @param constraints Atoms of the same level such that @ref sample cannot be extended for the highest variable without making one atom false. Note that this property is not checked.
 * @param sample A sample such that all but the highest variable in @ref constraints are assigned.
 * @return A sampled derivation which contains the information to reproduce the conflict. 
 */
template<cadcells::operators::op op, representation::CoveringHeuristic covering_heuristic>
std::optional<datastructures::SampledDerivationRef<typename operators::PropertiesSet<op>::type>> get_level_covering(datastructures::Projections& proj, const std::vector<Atom>& constraints, const Assignment& sample) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.algorithms.onecell", constraints << ", " << sample);
    std::vector<datastructures::SampledDerivationRef<typename operators::PropertiesSet<op>::type>> unsat_cells;
    for (const auto& c : constraints) {
        auto intervals = get_unsat_intervals<op>(c, proj, sample);
        unsat_cells.insert(unsat_cells.end(), intervals.begin(), intervals.end());
    }

    SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Computing covering representation");
    auto covering_repr = representation::covering<covering_heuristic>::compute(unsat_cells); // TODO distinguish between: not enough interval for covering and mccallum fails
    if (!covering_repr) {
        return std::nullopt;
    }
    SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got representation " << *covering_repr);

    SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Compute covering projection");
    auto cell_derivs = covering_repr->sampled_derivations();
    datastructures::merge_underlying(cell_derivs);
    if (!operators::project_covering_properties<op>(*covering_repr)) return std::nullopt;

    return covering_repr->cells.front().derivation->underlying().sampled_ref();
}

}