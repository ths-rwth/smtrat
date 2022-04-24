#include "approximation/CellApproximator.h"

namespace smtrat::cadcells::representation {

using IR = datastructures::IndexedRoot;

enum ApxStrategy {ONLY_BOUNDS, BETWEEN}; // For CHAIN, only BETWEEN makes sense, for LDB we might need another option
constexpr ApxStrategy approximation_strategy = ApxStrategy::ONLY_BOUNDS;

template <>
struct cell<CellHeuristic::BIGGEST_CELL_APPROXIMATION> {
    template<typename T>
    static std::optional<datastructures::CellRepresentation<T>> compute(datastructures::SampledDerivationRef<T>& der) {
        approximation::CellApproximator apx(der);

        datastructures::CellRepresentation<T> response(*der);
        if (approximation_strategy == ApxStrategy::ONLY_BOUNDS) {
            response.description = apx.compute_cell();
        } else {
            response.description = compute_simplest_cell(der->proj(), der->cell());
        }

        if (der->cell().is_section()) {
            compute_section_all_equational(der, response);
        } else { // sector
            if (!der->delin().nullified().empty()) return std::nullopt;
            // instead of only approximating the cell bounds, we could insert approximations in the following part
            // res(p,q) for high degree polynoimals p,q would be replaced by res(p,r) and res(r,q)
            // this leads to more polynomials than in the other approximation, but the immedeate cell bounds might be more accurate
            if (!der->cell().lower_unbounded()) {
                auto it = der->cell().lower();
                while(true) {
                    for (const auto& ir : it->second) {
                        if (ir != *response.description.lower()) {
                            if (approximation_strategy == ApxStrategy::BETWEEN) {
                                if (approximation::criteria::pair(der->proj(), ir, *response.description.lower())) {
                                    // TODO: what if the two root expressions correspond to the same root?
                                    IR ir_between = apx.approximate_between(ir, *response.description.lower(), it->first, der->cell().lower()->first);
                                    response.ordering.add_below(*response.description.lower(), ir_between);
                                    response.ordering.add_below(ir_between, ir);
                                    // from here on, this is technically no longer in the biggest-cell-structure
                                } else response.ordering.add_below(*response.description.lower(), ir);
                            } else response.ordering.add_below(*response.description.lower(), ir);
                        } 
                    }
                    if (it != der->delin().roots().begin()) it--;
                    else break;
                }
            }
            if (!der->cell().upper_unbounded()) {
                auto it = der->cell().upper();
                while(it != der->delin().roots().end()) {
                    for (const auto& ir : it->second) {
                        if (ir != *response.description.upper()) {
                            if (approximation_strategy == ApxStrategy::BETWEEN) {
                                if (approximation::criteria::pair(der->proj(), *response.description.upper(), ir)) {
                                    // TODO: what if the two root expressions correspond to the same root?
                                    IR ir_between = apx.approximate_between(*response.description.upper(), ir, der->cell().upper()->first, it->first);
                                    response.ordering.add_above(*response.description.upper(), ir_between);
                                    response.ordering.add_above(ir_between, ir);
                                    // from here on, this is technically no longer in the biggest-cell-structure
                                } else response.ordering.add_above(*response.description.upper(), ir);
                            } else response.ordering.add_above(*response.description.upper(), ir);
                            response.ordering.add_above(*response.description.upper(), ir);
                        }
                    }
                    it++;
                }
            }
        }
        return response;
    }
};

}