#include "onecell.h"
#include "helper.h"

#include "../operators/operator_mccallum.h"
#include "../representation/heuristics.h"

#include "level_covering.h"
#include "delineation.h"

namespace smtrat::cadcells::algorithms {

// constexpr auto cell_heuristic = representation::BIGGEST_CELL;
// constexpr auto cell_heuristic = representation::CHAIN_EQ;
// constexpr auto cell_heuristic = representation::LOWEST_DEGREE_BARRIERS_EQ;
constexpr auto cell_heuristic = representation::LOWEST_DEGREE_BARRIERS;
constexpr auto covering_heuristic = representation::DEFAULT_COVERING;
constexpr auto op = operators::op::mccallum;
constexpr bool use_delineation = false; 

using PropSet = operators::PropertiesSet<op>::type;

std::optional<std::pair<FormulasT, FormulaT>> onecell(const FormulasT& constraints, const VariableOrdering& vars, const Assignment& sample) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.algorithms.onecell", constraints << ", " << vars << ", " << sample);
    datastructures::PolyPool pool(vars);
    datastructures::Projections proj(pool);

    std::optional<datastructures::SampledDerivationRef<PropSet>> first_level_res;
    if (use_delineation) {
        auto first_level_res = get_delineation<op, representation::CHAIN>(proj, constraints, sample);
    } else {
        auto first_level_res = get_level_covering<op, covering_heuristic>(proj, constraints, sample);
    }
    if (!first_level_res) {
        return std::nullopt;
    }
    datastructures::SampledDerivationRef<PropSet> cell_deriv = *first_level_res;

    FormulasT description;
    while (cell_deriv->level() > 0) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Constructing cell on level " << cell_deriv->level());

        SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Project properties");
        if (!operators::project_cell_properties<op>(*cell_deriv)) {
            SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Could not project properties");
            return std::nullopt;
        }
        operators::project_basic_properties<op>(*cell_deriv->delineated());
        SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Delineate properties");
        operators::delineate_properties<op>(*cell_deriv->delineated());
        cell_deriv->delineate_cell();
        SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got interval " << cell_deriv->cell() << " wrt " << cell_deriv->delin());
        SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Compute cell representation");
        auto cell_repr = representation::cell<cell_heuristic>::compute(cell_deriv);
        if (!cell_repr) {
            SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Could not compute representation");
            return std::nullopt;
        }
        SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got representation " << *cell_repr);
        SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Project cell");
        operators::project_delineated_cell_properties<op>(*cell_repr);

        description.emplace_back(helper::to_formula(proj.polys(), cell_deriv->main_var(),cell_repr->description));
        proj.clear_assignment_cache(cell_deriv->sample());
        cell_deriv = cell_deriv->underlying().sampled_ref();
        proj.clear_cache(cell_deriv->level()+2);
    }
    proj.clear_assignment_cache(empty_assignment);

    return std::make_pair(constraints, FormulaT(carl::FormulaType::AND, std::move(description)));
}

}