#include "approximation/CellApproximator.h"

namespace smtrat::cadcells::representation {

using IR = datastructures::IndexedRoot;

// the following distinction is better to implement as different cell heuristics
// enum ApxStrategy {ONLY_BOUNDS, BETWEEN}; // For CHAIN, only BETWEEN makes sense, for LDB we might need another option
// constexpr ApxStrategy approximation_strategy = ApxStrategy::ONLY_BOUNDS;

template <>
struct cell<CellHeuristic::BIGGEST_CELL_APPROXIMATION> {
    template<typename T>
    static std::optional<datastructures::CellRepresentation<T>> compute(datastructures::SampledDerivationRef<T>& der) {
        approximation::CellApproximator apx(der);

        datastructures::CellRepresentation<T> response(der);
        response.description = apx.compute_cell();

        if (der->cell().is_section()) {
            compute_section_all_equational(der, response);
        } else { // sector
            datastructures::Delineation reduced_delineation;
            util::PolyDelineations poly_delins;
            util::decompose(der->delin(), der->cell(), reduced_delineation, poly_delins);
            auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
            auto res = util::simplest_biggest_cell_ordering(der->proj(), reduced_delineation, reduced_cell, response.description);
            if (!res) return std::nullopt;
            response.ordering = *res;
            for (const auto& poly_delin : poly_delins.data) {
                add_biggest_cell_ordering(response.ordering, poly_delin.first, poly_delin.second);
            }
        }
        maintain_connectedness(der, response);
        return response;
    }
};

}