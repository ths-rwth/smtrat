#pragma once

#include "combinatorialopt/ordering.h"

namespace smtrat::cadcells::representation::cell_heuristics {

template<combinatorialopt::ResultantCostMetric M>
struct CombinatorialOptimization {
    template<typename T>
    static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
        datastructures::CellRepresentation<T> response(der);
        datastructures::Delineation reduced_delineation = der->delin();
        auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
        response.description = util::compute_simplest_cell(der->level(), der->proj(), reduced_cell, false);

        if (der->cell().is_section()) { // section case
            SMTRAT_LOG_DEBUG("smtrat.cadcells.representation", "Computing optimal ordering (section case).");
            util::PolyDelineations poly_delins;
            util::decompose(reduced_delineation, reduced_cell, poly_delins);
            combinatorialopt::compute_optimal_ordering<M>(der->proj(),
                                        reduced_delineation,
                                        reduced_cell,
                                        response.description,
                                        response.ordering,
                                        response.equational);
        } else { // sector case
            SMTRAT_LOG_DEBUG("smtrat.cadcells.representation", "Computing optimal ordering (sector case).");
            handle_cell_reduction(reduced_delineation, reduced_cell, response);
            combinatorialopt::compute_optimal_ordering<M>(der->proj(),
                                        reduced_delineation,
                                        reduced_cell,
                                        response.description,
                                        response.ordering,
                                        response.equational);
            handle_connectedness(der, response, false);
        }
        handle_ordering_polys(der, response);
        SMTRAT_STATISTICS_CALL(statistics().got_representation_equational(der->level(), response.equational.size()));
        return response;
    }
};


}