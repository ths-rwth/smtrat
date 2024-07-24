#pragma once



namespace smtrat::cadcells::algorithms {

/**
 * @brief Single cell construction algorithm.
 * 
 * @tparam op The operator.
 * @tparam cell_heuristic The cell heuristic.
 * @param cell_deriv A derivation object to construct the cell from.
 * @return A vector of pairs of variables and their symbolic intervals on success or std::nullopt otherwise.
 */
template<typename op, typename cell_heuristic>
std::optional<std::pair<carl::Variable, datastructures::SymbolicInterval>> get_interval(datastructures::SampledDerivationRef<typename op::PropertiesSet>& cell_deriv) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Constructing cell on level " << cell_deriv->level());

    SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Project properties");
    if (!op::project_basic_properties(*cell_deriv)) return std::nullopt;
    SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Delineate properties");
    op::delineate_properties(*cell_deriv);
    cell_deriv->delineate_cell();
    SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got interval " << cell_deriv->cell() << " wrt " << cell_deriv->delin());
    SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Compute cell representation");
    auto cell_repr = cell_heuristic::compute(cell_deriv);
    SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got representation " << cell_repr);
    if (cell_deriv->level() > 1) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Project cell");
        if (!op::project_cell_properties(cell_repr)) return std::nullopt;
    }

    return std::make_pair(cell_deriv->main_var(),cell_repr.description);
}

}