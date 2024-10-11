#pragma once

#include "approximation/ApproximationSettings.h"
#include "approximation/ran_approximation.h"
#include "approximation/polynomials.h"
#include "approximation/criteria.h"
#include "util.h"

namespace smtrat::cadcells::representation::approximation {

using IR = datastructures::IndexedRoot;
using RF = datastructures::RootFunction;

template<typename Settings, typename T>
datastructures::SymbolicInterval approximate_interval(datastructures::SampledDerivationRef<T>& der) {
    const auto& cell = der->cell();
    auto& proj = der->proj();
    auto& criteria = Settings::Criteria::get();

    if (cell.is_section()) { // Section case as before
        return datastructures::SymbolicInterval(util::simplest_bound(proj, cell.lower()->second));
    }
    
    if (cell.lower_unbounded() && cell.upper_unbounded()) {
        return datastructures::SymbolicInterval();
    }
    
    if (cell.lower_unbounded()) {
        IR upper = util::simplest_bound(proj, cell.upper()->second);
        if (criteria.side(proj, upper, cell.upper(), der->delin().roots().end())) {
            RF upper_apx = Settings::method::bound(upper, cell.upper()->first, der, false);
            criteria.did_approximation();
            SMTRAT_STATISTICS_CALL(apx_statistics().approximated(proj.degree(upper.poly)));
            return datastructures::SymbolicInterval(datastructures::Bound::infty(), datastructures::Bound::strict(upper_apx));
        }
        return datastructures::SymbolicInterval(datastructures::Bound::infty(), datastructures::Bound::strict(upper));
    }
    
    if (cell.upper_unbounded()) {
        IR lower = util::simplest_bound(proj, cell.lower()->second);
        if (criteria.side(proj, lower, der->delin().roots().begin(), der->delin().roots().end())){
            RF lower_apx = Settings::method::bound(lower, cell.lower()->first, der, true);
            criteria.did_approximation();
            SMTRAT_STATISTICS_CALL(apx_statistics().approximated(proj.degree(lower.poly)));
            return datastructures::SymbolicInterval(datastructures::Bound::strict(lower_apx), datastructures::Bound::infty());
        }
        return datastructures::SymbolicInterval(datastructures::Bound::strict(lower), datastructures::Bound::infty());
    }
    
    IR lower = util::simplest_bound(proj, cell.lower()->second);
    IR upper = util::simplest_bound(proj, cell.upper()->second);
    datastructures::Bound l = datastructures::Bound::strict(lower);
    datastructures::Bound u = datastructures::Bound::strict(upper);
    if (criteria.side(proj, upper, cell.upper(), der->delin().roots().end())){
        u = datastructures::Bound::strict(Settings::method::bound(upper, cell.upper()->first, der, false));
        criteria.did_approximation();
        SMTRAT_STATISTICS_CALL(apx_statistics().approximated(proj.degree(upper.poly)));
    }
    if (criteria.side(proj, lower, der->delin().roots().begin(), cell.upper())) {
        l = datastructures::Bound::strict(Settings::method::bound(lower, cell.lower()->first, der, true));
        criteria.did_approximation();
        SMTRAT_STATISTICS_CALL(apx_statistics().approximated(proj.degree(lower.poly)));
    }
    return datastructures::SymbolicInterval(l, u);
}


template<typename Settings, typename T>
void insert_approximation_above(datastructures::SampledDerivationRef<T>& der, datastructures::Delineation& delin, const datastructures::DelineationInterval& cell, bool force_inside=false) {
    assert(!cell.upper_unbounded());
    auto it = cell.upper();
    auto& proj = der->proj();

    for (const auto& ir : it->second) {
        // if any poly at the bound is linear, do nothing
        if (proj.degree(ir.root.poly) <= 1) return;
    }
    
    if (it->second.size() > 1 || force_inside) {
        // if there are multiple polys at the bound, apx inside
        Rational new_root = SampleSimple::above(der->main_var_sample(), cell.upper()->first);
        Polynomial var_poly = Polynomial(proj.polys().context(), der->main_var());
        IR new_bound(
            proj.polys()(carl::get_denom(new_root)*var_poly - carl::get_num(new_root)), 1
        );
        delin.add_root(RAN(new_root), datastructures::TaggedIndexedRoot{new_bound});
        SMTRAT_STATISTICS_CALL(apx_statistics().approximated(proj.degree(2)));
        return;
    }

    // if there is a non-linear poly outside the bound before a linear one, apx outside
    assert(it->second.size() == 1);
    IR bound = it->second.front().root;
    ++it;
    while (it != delin.roots().end()) {
        for (const auto& ir : it->second) {
            if (proj.degree(ir.root.poly) <= 1) return; // linear bound before anything was approximated
            if (!Settings::Criteria::get().poly_pair(proj, bound, ir.root)) continue;
            // do apx
            Rational new_root = SampleSimple::above(cell.upper()->first, it->first);
            Polynomial var_poly = Polynomial(proj.polys().context(), der->main_var());
            IR new_bound(
                proj.polys()(carl::get_denom(new_root)*var_poly - carl::get_num(new_root)), 1
            );
            delin.add_root(RAN(new_root), datastructures::TaggedIndexedRoot{new_bound});
            SMTRAT_STATISTICS_CALL(apx_statistics().approximated(proj.degree(bound.poly)));
            return;
        }
    }
}

template<typename Settings, typename T>
void insert_approximation_below(datastructures::SampledDerivationRef<T>& der, datastructures::Delineation& delin, const datastructures::DelineationInterval& cell, bool force_inside=false) {
    assert(!cell.lower_unbounded());
    auto it = cell.lower();
    auto& proj = der->proj();

    for (const auto& ir : it->second) {
        // if any poly at the bound is linear, do nothing
        if (proj.degree(ir.root.poly) <= 1) return;
    }
    
    if (it->second.size() > 1 || force_inside) {
        // if there are multiple polys at the bound, apx inside
        Rational new_root = SampleSimple::below(der->main_var_sample(), cell.lower()->first);
        Polynomial var_poly = Polynomial(proj.polys().context(), der->main_var());
        IR new_bound(
            proj.polys()(carl::get_denom(new_root)*var_poly - carl::get_num(new_root)), 1
        );
        delin.add_root(RAN(new_root), datastructures::TaggedIndexedRoot{new_bound});
        SMTRAT_STATISTICS_CALL(apx_statistics().approximated(2));
        return;
    }

    // if there is a non-linear poly outside the bound before a linear one, apx outside
    assert(it->second.size() == 1);
    IR bound = it->second.front().root;
    while (it != delin.roots().begin()) {
        --it;
        for (const auto& ir : it->second) {
            if (proj.degree(ir.root.poly) <= 1) return; // linear bound before anything was approximated
            if (!Settings::Criteria::get().poly_pair(proj, bound, ir.root)) continue;
            // do apx
            Rational new_root = SampleSimple::below(cell.lower()->first, it->first);
            Polynomial var_poly = Polynomial(proj.polys().context(), der->main_var());
            IR new_bound(
                proj.polys()(carl::get_denom(new_root)*var_poly - carl::get_num(new_root)), 1
            );
            delin.add_root(RAN(new_root), datastructures::TaggedIndexedRoot{new_bound});
            SMTRAT_STATISTICS_CALL(apx_statistics().approximated(proj.degree(bound.poly)));
            return;
        }
    }
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


template<typename Settings>
struct InAndOutApproximation {
    template<typename T>
    static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
        bool enable_weak = true;

        datastructures::Delineation reduced_delineation = der->delin();
        auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());

        if (reduced_cell.is_sector()) {
            // insert approximations into the delineation
            if (reduced_cell.lower_unbounded()) {
                if (!reduced_cell.upper_unbounded()) {
                    // (-oo,u)
                    approximation::insert_approximation_above<Settings>(der, reduced_delineation, reduced_cell);
                }
                // (-oo,oo) -> do nothing
            } else {
                if (reduced_cell.upper_unbounded()) {
                    // (l,oo)
                    approximation::insert_approximation_below<Settings>(der, reduced_delineation, reduced_cell);
                } else {
                    // (l,u)
                    approximation::IR l = util::simplest_bound(der->proj(), reduced_cell.lower()->second);
                    approximation::IR u = util::simplest_bound(der->proj(), reduced_cell.lower()->second);
                    bool l_inside = (der->proj().degree(l.poly) > der->proj().degree(u.poly));
                    approximation::insert_approximation_above<Settings>(der, reduced_delineation, reduced_cell, !l_inside);
                    reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
                    approximation::insert_approximation_below<Settings>(der, reduced_delineation, reduced_cell, l_inside);
                }
            }
            reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
        }

        datastructures::CellRepresentation<T> response(der);
        response.description = util::compute_simplest_cell(der->level(), der->proj(), der->cell());
        if (der->cell().is_section()) {
            handle_local_del_simplify_non_independent(reduced_delineation);
            handle_local_del(der, reduced_delineation, response);
            util::PolyDelineations poly_delins;
            util::decompose(reduced_delineation, reduced_cell, poly_delins);
            util::simplest_ldb_ordering(
                der->proj(), reduced_delineation, reduced_cell, response.description,
                response.ordering, response.equational, enable_weak, false
            );
            for (const auto& poly_delin : poly_delins.data) {
                if (response.equational.contains(poly_delin.first)) continue;
                chain_ordering(poly_delin.first, poly_delin.second, response.ordering);
            }
            for (const auto& poly : der->delin().nullified()) {
                response.equational.insert(poly);
            }
            for (const auto& poly : der->delin().nonzero()) {
                response.equational.insert(poly);
            }
        } else { // sector
            handle_local_del(der, reduced_delineation, response);
            handle_cell_reduction(reduced_delineation, reduced_cell, response);
            util::simplest_ldb_ordering(
                der->proj(), reduced_delineation, reduced_cell, response.description,
                response.ordering, response.equational, enable_weak, false
            );
        }
        handle_connectedness(der, response);
        handle_ordering_polys(der, response);
        SMTRAT_STATISTICS_CALL(statistics().got_representation_equational(der->level(), response.equational.size()));
        return response;
    }
};

}