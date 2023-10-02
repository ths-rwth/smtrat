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
        bool enable_weak = false;

        approximation::CellApproximator apx(der);

        datastructures::CellRepresentation<T> response(der);
        response.description = apx.compute_cell();

        if (der->cell().is_section()) {
            compute_section_all_equational(der, response);
        } else { // sector
            datastructures::Delineation reduced_delineation = der->delin();
            auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
            for (const auto poly : util::get_local_del_polys(reduced_delineation)) {
                util::local_del_ordering(der->proj(), poly, der->sample(), reduced_delineation, response.description, response.ordering);
            }
            util::PolyDelineations poly_delins;
            util::decompose(reduced_delineation, reduced_cell, poly_delins);
            util::simplest_biggest_cell_ordering(der->proj(), reduced_delineation, reduced_cell, response.description, response.ordering, enable_weak);
            for (const auto& poly_delin : poly_delins.data) {
                chain_ordering(poly_delin.first, poly_delin.second, response.ordering);
            }
        }
        maintain_connectedness(der, response, enable_weak);
        return response;
    }
};

}