#include "unsat_intervals.h"

namespace smtrat::cadcells::algorithms {

template<cadcells::operators::op op, representation::CoveringHeuristic covering_heuristic>
std::optional<datastructures::SampledDerivationRef<typename operators::PropertiesSet<op>::type>> get_level_covering(datastructures::Projections& proj, const FormulasT& constraints, const Assignment& sample) {
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
    operators::project_covering_properties<op>(*covering_repr);

    return covering_repr->cells.front().derivation.underlying().sampled_ref();
}

}