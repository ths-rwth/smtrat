#include "approximation/CellApproximator.h"

namespace smtrat::cadcells::representation {

using IR = datastructures::IndexedRoot;

// the following distinction is better to implement as different cell heuristics
// enum ApxStrategy {ONLY_BOUNDS, BETWEEN}; // For CHAIN, only BETWEEN makes sense, for LDB we might need another option
// constexpr ApxStrategy approximation_strategy = ApxStrategy::ONLY_BOUNDS;

template <>
struct cell<CellHeuristic::BIGGEST_CELL_APPROXIMATION> {
    template<typename T>
    static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
        bool enable_weak = true;
        LocalDelMode ldel_mode = LocalDelMode::ALL;

        datastructures::CellRepresentation<T> response(der);
        datastructures::Delineation reduced_delineation = der->delin();
        if (ldel_mode == LocalDelMode::ONLY_INDEPENDENT) {
            handle_local_del_simplify_non_independent(reduced_delineation);
        } else if (ldel_mode == LocalDelMode::SIMPLIFY) {
            handle_local_del_simplify_all(reduced_delineation);
        }
        auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());

        approximation::CellApproximator apx(der);
        response.description = apx.compute_cell();

        response.ordering.biggest_cell_wrt = response.description;
        if (der->cell().is_section()) {
            handle_local_del_simplify_non_independent(reduced_delineation);
            handle_local_del(der, reduced_delineation, response);
            handle_section_all_equational(reduced_delineation, response);
        } else { // sector
            handle_local_del(der, reduced_delineation, response);
            handle_cell_reduction(reduced_delineation, reduced_cell, response);
            util::simplest_biggest_cell_ordering(der->proj(), reduced_delineation, reduced_cell, response.description, response.ordering, enable_weak);
        }
        handle_connectedness(der, response, enable_weak);
        handle_ordering_polys(der, response);
        return response;
    }
};

}