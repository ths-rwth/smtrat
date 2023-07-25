#pragma once

#include "properties.h"
#include "../datastructures/derivation.h"

namespace smtrat::cadcells::operators::rules {

template<typename P>
bool poly_del_pdel(datastructures::SampledDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "del(" << poly << ")");
    deriv.insert(properties::poly_proj_del{ poly });
    if (deriv.proj().num_roots(deriv.sample(), poly) > 0 || deriv.proj().is_ldcf_zero(deriv.sample(), poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> del(" << poly << ") <= proj_del(" << poly << ") && sgn_inv(ldcf(" << poly << ") [" << deriv.proj().ldcf(poly) << "])");
        deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) });
    } else {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> del(" << poly << ") <= proj_del(" << poly << ")");
    }
    return true;
}

template<typename P>
bool poly_proj_del(datastructures::SampledDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "proj_del(" << poly << ")");
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> proj_del(" << poly << ") <= non_null(" << poly << ") && ord_inv(disc(" << poly << ") [" << deriv.proj().disc(poly) << "]) && cell_connected(" << (poly.level-1) << ")");
    deriv.insert(properties::poly_ord_inv{ deriv.proj().disc(poly) });
    deriv.insert(properties::cell_connected{ poly.level-1 });
    if (!poly_non_null(deriv, poly)) return false;
    return true;
}

template<typename P>
void poly_irreducible_ord_inv_pdel(datastructures::SampledDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "ord_inv(" << poly << "), " << poly << " irreducible");
    if (deriv.proj().is_const(poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv(" << poly << ") <= " << poly << " const");
    } else {
        if (deriv.proj().is_zero(deriv.sample(), poly)) {
            SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv(" << poly << ") <= proj_del(" << poly << ") && sgn_inv(" << poly << ") && cell_connected(" << poly.level << ")");
            deriv.insert(properties::poly_proj_del{ poly });
            deriv.insert(properties::cell_connected{ poly.level });
        } else {
            SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv(" << poly << ") <= " << poly << "(" << deriv.sample() << ") != 0 && sgn_inv(" << poly << ")");
        }
        deriv.insert(properties::poly_irreducible_sgn_inv{ poly });
    }
}

template<typename P>
void poly_ord_inv_pdel(datastructures::SampledDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "ord_inv(" << poly << ")");
    if (deriv.proj().is_const(poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv(" << poly << ") <= " << poly << " const");
    } else {
        auto factors = deriv.proj().factors_nonconst(poly);
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv(" << poly << ") <= ord_inv(factors(" << poly << ")) <=> ord_inv(" << factors << ")");
        for (const auto& factor : factors) {
            poly_irreducible_ord_inv_pdel(deriv, factor);
        }
    }   
}

template<typename P>
void root_ordering_holds_pdel(datastructures::SampledDerivation<P>& deriv, const datastructures::IndexedRootOrdering& ordering) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "ir_ord(" << ordering << ", " << deriv.sample() << ")");
    assert(ordering.is_projective());
    deriv.insert(properties::cell_connected{ deriv.level() });
    for (const auto& rel : ordering.data()) {
        assert(rel.first.is_root() && rel.second.is_root());
        auto& first = rel.first.root();
        auto& second = rel.second.root();
        if (first.poly != second.poly) {
            //assert(rel.is_strict || (ordering.holds_transitive(first,second,false) && ordering.holds_transitive(second,first,false))); // not supported
            assert(deriv.contains(properties::poly_proj_del{ first.poly }));
            assert(deriv.contains(properties::poly_proj_del{ second.poly }));
            deriv.insert(properties::poly_ord_inv{ deriv.proj().res(first.poly, second.poly) });
        }
    }
}

template<typename P>
void poly_irreducible_sgn_inv_pdel(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& cell, const datastructures::IndexedRootOrdering& ordering, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "sgn_inv(" << poly << "), " << poly << " irreducible");
    if (ordering.non_projective_polys().find(poly) != ordering.non_projective_polys().end()) {
        deriv.insert(properties::poly_del{ poly });
    } else if (cell.lower().is_infty() || cell.upper().is_infty()) {
        deriv.insert(properties::poly_del{ poly });
    } else {
        assert(deriv.contains(properties::poly_proj_del{ poly }));
    }
}


}