#pragma once

#include "approximation/ApproximationSettings.h"

namespace smtrat::cadcells::representation::approximation {

using IR = datastructures::IndexedRoot;
using RF = datastructures::RootFunction;

template<typename Settings, typename T>
datastructures::SymbolicInterval approximate_interval(datastructures::SampledDerivationRef<T>& der) {
    const auto& cell = der->cell();
    auto& proj = der->proj();

    if (cell.is_section()) { // Section case as before
        return datastructures::SymbolicInterval(util::simplest_bound(proj, cell.lower()->second));
    }
    
    if (cell.lower_unbounded() && cell.upper_unbounded()) {
        return datastructures::SymbolicInterval();
    }
    
    if (cell.lower_unbounded()) {
        IR upper = util::simplest_bound(proj, cell.upper()->second);
        if (Settings::Criteria::side(proj, upper, cell.upper(), der->delin().roots().end())) {
            RF upper_apx = Settings::method::bound(upper, cell.upper()->first, der, false);
            return datastructures::SymbolicInterval(datastructures::Bound::infty(), datastructures::Bound::strict(upper_apx));
        }
        return datastructures::SymbolicInterval(datastructures::Bound::infty(), datastructures::Bound::strict(upper));
    }
    
    if (cell.upper_unbounded()) {
        IR lower = util::simplest_bound(proj, cell.lower()->second);
        if (Settings::Criteria::side(proj, lower, der->delin().roots().begin(), der->delin().roots().end())){
            RF lower_apx = Settings::method::bound(lower, cell.lower()->first, der, true);
            return datastructures::SymbolicInterval(datastructures::Bound::strict(lower_apx), datastructures::Bound::infty());
        }
        return datastructures::SymbolicInterval(datastructures::Bound::strict(lower), datastructures::Bound::infty());
    }
    
    IR lower = util::simplest_bound(proj, cell.lower()->second);
    IR upper = util::simplest_bound(proj, cell.upper()->second);
    RF lower_rf = lower;
    RF upper_rf = upper;
    if (Settings::Criteria::side(proj, upper, cell.upper(), der->delin().roots().end()))
        upper_rf = Settings::method::bound(upper, cell.upper()->first, der, false);
    if (Settings::Criteria::side(proj, lower, der->delin().roots().begin(), cell.upper()))
        lower_rf = Settings::method::bound(lower, cell.lower()->first, der, true);
    return datastructures::SymbolicInterval(datastructures::Bound::strict(lower_rf), datastructures::Bound::strict(upper_rf));
}

}

namespace smtrat::cadcells::representation::cell_heuristics {

template<typename Settings>
struct BiggestCellApproximation {
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

        response.description = approximation::approximate_interval<Settings>(der);

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