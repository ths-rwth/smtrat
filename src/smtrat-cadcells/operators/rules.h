#pragma once

#include "properties.h"
#include "properties_util.h"
#include "../datastructures/derivation.h"

/**
 * Implementation of derivation rules.
 * 
 * Each rule is realized by a function which works on a derivation object. The parameters of the respective properties are passed as function parameter. The function realizing a derivation rule might either call other derivation rules or add properties to the given derivation.
 * 
 */
namespace smtrat::cadcells::operators::rules {

template<typename P>
bool poly_non_null(datastructures::SampledDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "non_null(" << poly << ")");
    if(deriv.proj().is_nullified(deriv.sample(), poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "non_null(" << poly << ") <= false");
        return false;
    } else if (deriv.proj().has_const_coeff(poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "non_null(" << poly << ") <= " << poly << " has const coeff");
    } else if (!deriv.proj().is_ldcf_zero(deriv.sample(), poly) && deriv.contains(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) } )) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "non_null(" << poly << ") <= ldcf(" << poly << ")(" << deriv.sample() << ")!=0 && sgn_inv(ldcf(" << poly << ") [" << deriv.proj().ldcf(poly) << "])");
    } else if (
        /* deriv.proj().know_disc(poly) && */ deriv.proj().degree(poly) > 1 && !deriv.proj().is_disc_zero(deriv.sample(), poly) &&
        (deriv.contains(properties::poly_sgn_inv{ deriv.proj().disc(poly) }) || deriv.contains(properties::poly_ord_inv{ deriv.proj().disc(poly) }))
    ) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "non_null(" << poly << ") <= disc(" << poly << ")(" << deriv.sample() << ")!=0 && sgn_inv(disc(" << poly << ") [" << deriv.proj().disc(poly) << "])");
    } else {
        auto coeff = deriv.proj().simplest_nonzero_coeff(deriv.sample(), poly, [&](const Polynomial& a, const Polynomial& b) {
            if (deriv.proj().known(a) && deriv.contains( properties::poly_sgn_inv { deriv.proj().polys()(a)} )) return true;
            if (deriv.proj().known(b) && deriv.contains( properties::poly_sgn_inv { deriv.proj().polys()(b)} )) return true;
            return carl::level_of(a) < carl::level_of(b) || (carl::level_of(a) == carl::level_of(b) && a.total_degree() < b.total_degree());
        });
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "non_null(" << poly << ") <= sgn_inv(" << coeff << ") && " << coeff << " in coeff(" << poly << ")");
        deriv.insert(properties::poly_sgn_inv{ coeff });
    }
    return true;
}

template<typename P>
bool poly_del(datastructures::SampledDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "del(" << poly << ")");
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> del(" << poly << ") <= non_null(" << poly << ") && ord_inv(disc(" << poly << ") [" << deriv.proj().disc(poly) << "]) && sgn_inv(ldcf(" << poly << ") [" << deriv.proj().ldcf(poly) << "]) && cell_connected(" << (poly.base_level) << ")");
    deriv.insert(properties::poly_ord_inv{ deriv.proj().disc(poly) });
    deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) });
    deriv.insert(properties::cell_connected{ poly.base_level });
    if (!poly_non_null(deriv, poly)) return false;
    return true;
}

template<typename P>
void poly_irreducible_ord_inv(datastructures::SampledDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "ord_inv(" << poly << "), " << poly << " irreducible");
    if (deriv.proj().is_const(poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv(" << poly << ") <= " << poly << " const");
    } else {
        if (deriv.proj().is_zero(deriv.sample(), poly)) {
            SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv(" << poly << ") <= del(" << poly << ") && sgn_inv(" << poly << ") && cell_connected(" << poly.level << ")");
            deriv.insert(properties::poly_del{ poly });
            deriv.insert(properties::cell_connected{ poly.level });
        } else {
            SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv(" << poly << ") <= " << poly << "(" << deriv.sample() << ") != 0 && sgn_inv(" << poly << ")");
        }
        deriv.insert(properties::poly_irreducible_sgn_inv{ poly });
    }
}

template<typename P>
void poly_ord_inv(datastructures::SampledDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "ord_inv(" << poly << ")");
    if (deriv.proj().is_const(poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv(" << poly << ") <= " << poly << " const");
    } else {
        auto factors = deriv.proj().factors_nonconst(poly);
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv(" << poly << ") <= ord_inv(factors(" << poly << ")) <=> ord_inv(" << factors << ")");
        for (const auto& factor : factors) {
            poly_irreducible_ord_inv(deriv, factor);
        }
    }   
}

template<typename P>
void poly_sgn_inv(datastructures::SampledDerivation<P>& deriv, datastructures::PolyRef poly, bool skip_if_ord_inv = true) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "sgn_inv(" << poly << ")");
    if (deriv.proj().is_const(poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> sgn_inv(" << poly << ") <= " << poly << " const");
    } else if (skip_if_ord_inv && deriv.contains(properties::poly_ord_inv{ poly })) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> sgn_inv(" << poly << ") <= ord_inv(" << poly << ")");
    } else { 
        std::optional<datastructures::PolyRef> lowest_zero_factor;
        for (const auto& factor : deriv.proj().factors_nonconst(poly)) {
            if (deriv.proj().is_zero(deriv.sample(), factor)) {
                if (lowest_zero_factor == std::nullopt ||
                    factor.level < lowest_zero_factor->level ||
                    (factor.level == lowest_zero_factor->level && (factor.level == poly.level && deriv.proj().is_nullified(deriv.underlying_sample(), factor) && !deriv.proj().is_nullified(deriv.underlying_sample(), *lowest_zero_factor))) ||
                    (factor.level == lowest_zero_factor->level && (factor.level != poly.level || (deriv.proj().is_nullified(deriv.underlying_sample(), factor) && deriv.proj().is_nullified(deriv.underlying_sample(), *lowest_zero_factor))) && deriv.proj().total_degree(factor) < deriv.proj().total_degree(*lowest_zero_factor))
                    ) {
                    lowest_zero_factor = factor;
                }
            }
        }

        if (lowest_zero_factor) {
            SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> sgn_inv(" << poly << ") <= sgn_inv(" << *lowest_zero_factor << ") && " << *lowest_zero_factor << "("<< deriv.sample() <<")=0");
            deriv.insert(properties::poly_irreducible_sgn_inv{ *lowest_zero_factor });
        } else {
            SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> sgn_inv(" << poly << ") <= sgn_inv(factors(" << poly << ")) <=> sgn_inv(" << deriv.proj().factors_nonconst(poly) << ")");
            for (const auto& factor : deriv.proj().factors_nonconst(poly)) {
                deriv.insert(properties::poly_irreducible_sgn_inv{ factor });
            }
        }
    }
}

template<typename P>
void poly_irreducible_nonzero_sgn_inv(datastructures::DelineatedDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "sgn_inv(" << poly << "), " << poly << " irreducible and non-zero");
    assert(deriv.proj().num_roots(deriv.underlying_sample(), poly) == 0);
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> sgn_inv(" << poly << ") <= del(" << poly << ")");
    deriv.insert(properties::poly_del{ poly });
}

template<typename P>
void delineate(datastructures::DelineatedDerivation<P>& deriv, const properties::poly_irreducible_sgn_inv& prop) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "delineate(" << prop << ")");
    if (deriv.proj().is_nullified(deriv.underlying_sample(), prop.poly)) {
        deriv.delin().add_poly_nullified(prop.poly);
    } else {
        auto roots = deriv.proj().real_roots(deriv.underlying_sample(), prop.poly);
        if (roots.empty()) {
            deriv.delin().add_poly_nonzero(prop.poly);
        } else {
            for (size_t idx = 0; idx < roots.size(); idx++) {
                deriv.delin().add_root(roots[idx], datastructures::TaggedIndexedRoot{ datastructures::IndexedRoot(prop.poly, idx+1) });
            }
        }
    }
}

template<typename P>
void delineate(datastructures::DelineatedDerivation<P>& deriv, const properties::poly_irreducible_semi_sgn_inv& prop) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "delineate(" << prop << ")");
    if (deriv.proj().is_nullified(deriv.underlying_sample(), prop.poly)) {
        deriv.delin().add_poly_nullified(prop.poly);
    } else {
        auto roots = deriv.proj().real_roots(deriv.underlying_sample(), prop.poly);
        if (roots.empty()) {
            deriv.delin().add_poly_nonzero(prop.poly);
        } else {
            for (size_t idx = 0; idx < roots.size(); idx++) {
                deriv.delin().add_root(roots[idx], datastructures::TaggedIndexedRoot{datastructures::IndexedRoot(prop.poly, idx+1), true });
            }
        }
    }
}

template<typename P>
void cell_connected(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& cell, const datastructures::IndexedRootOrdering& ordering) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "connected(" << deriv.level() << ")");
    if (!cell.is_section() && !cell.lower().is_infty() && !cell.upper().is_infty()) {
        assert(ordering.is_projective() || ordering.holds_transitive(cell.lower().value(),cell.upper().value(), false));
    }
    deriv.insert(properties::cell_connected{ deriv.level()-1 });
}

template<typename P>
void cell_analytic_submanifold([[maybe_unused]] datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval&) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "an_sub(" << deriv.level() << ")");
}

template<typename P>
void poly_irreducible_sgn_inv_ec(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& cell, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "sgn_inv(" << poly << "), using EC");
    assert(cell.is_section());
    assert(deriv.contains(properties::poly_del{ cell.section_defining().poly }));
    deriv.insert(properties::cell_connected{ poly.base_level });
    if (cell.section_defining().poly != poly) {
        deriv.insert(properties::poly_ord_inv{ deriv.proj().res(cell.section_defining().poly, poly) });
    }
}

template<typename P>
void poly_irreducible_semi_sgn_inv_ec(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& cell, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "semi_sgn_inv(" << poly << "), using EC");
    poly_irreducible_sgn_inv_ec(deriv, cell, poly);
}

template<typename P>
void cell_represents(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& cell) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "repr(" << cell << ")");
    if (!cell.is_section()) {
        if (!cell.lower().is_infty()) {
            if (cell.lower().value().is_root()) {
                deriv.insert(properties::poly_del{ cell.lower().value().root().poly });
            } else {
                for (const auto& roots : cell.lower().value().roots()) {
                    for (const auto& root : roots) {
                        deriv.insert(properties::poly_del{ root.poly });
                    }
                }
            }
        }
        if (!cell.upper().is_infty()) {
            if (cell.upper().value().is_root()) {
                deriv.insert(properties::poly_del{ cell.upper().value().root().poly });
            } else {
                for (const auto& roots : cell.upper().value().roots()) {
                    for (const auto& root : roots) {
                        deriv.insert(properties::poly_del{ root.poly });
                    }
                }
            }
        }
    } else {
        deriv.insert(properties::poly_del{ cell.section_defining().poly });
    }
}

template<typename P>
void root_ordering_holds_pair(datastructures::SampledDerivation<P>& deriv, const datastructures::IndexedRoot& first, const datastructures::IndexedRoot& second) {
    if (first.poly != second.poly) {
        assert(deriv.contains(properties::poly_del{ first.poly }));
        assert(deriv.contains(properties::poly_del{ second.poly }));
        deriv.insert(properties::poly_ord_inv{ deriv.proj().res(first.poly, second.poly) });
    }
}

template<typename P>
void root_ordering_holds(datastructures::SampledDerivation<P>& deriv, const datastructures::IndexedRootOrdering& ordering) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "ir_ord(" << ordering << ", " << deriv.sample() << ")");
    deriv.insert(properties::cell_connected{ deriv.level() });
    for (const auto& rel : ordering.data()) {
        assert(rel.is_strict || (ordering.holds_transitive(rel.first,rel.second,false) && ordering.holds_transitive(rel.second,rel.first,false))); // not supported

        if (rel.first.is_root() && rel.second.is_root()) {
            root_ordering_holds_pair(deriv, rel.first.root(), rel.second.root());
        } else if (rel.first.is_root() && !rel.second.is_root()) {
            for (const auto& r2 : rel.second.roots()) {
                assert(r2.size() == 1);
                root_ordering_holds_pair(deriv, rel.first.root(), r2.front());
            }
        } else if (!rel.first.is_root() && rel.second.is_root()) {
            for (const auto& r1 : rel.first.roots()) {
                assert(r1.size() == 1);
                root_ordering_holds_pair(deriv, r1.front(), rel.second.root());
            }
        } else if (rel.first.is_cmaxmin() && rel.second.is_cminmax()) {
            for (const auto& r1 : rel.first.roots()) {
                assert(r1.size() == 1);
                for (const auto& r2 : rel.second.roots()) {
                    assert(r2.size() == 1);
                    root_ordering_holds_pair(deriv, r1.front(), r2.front());
                }
            }
        }
    }
}

template<typename P>
void poly_irreducible_sgn_inv(datastructures::SampledDerivation<P>& /*deriv*/, const datastructures::SymbolicInterval& /*cell*/, const datastructures::IndexedRootOrdering& /*ordering*/, [[maybe_unused]] datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "sgn_inv(" << poly << "), " << poly << " irreducible");
}

template<typename P>
void poly_irreducible_null_sgn_inv(datastructures::SampledDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "sgn_inv(" << poly << "), " << poly << " irreducible and nullified");
    assert(deriv.proj().is_nullified(deriv.underlying_sample(), poly));

    for (const auto coeff : deriv.proj().coeffs(poly)) {
        assert(deriv.proj().is_zero(deriv.sample(), coeff));
        deriv.insert(properties::poly_sgn_inv{ coeff });
    }
}

}

#include "rules_filter.h"
#include "rules_covering.h"
#include "rules_null.h" 