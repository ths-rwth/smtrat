#pragma once

#include "properties.h"
#include "../datastructures/derivation.h"

/**
 * Implementation of derivation rules.
 * 
 * Each rule is realized by a function which works on a derivation object. The parameters of the respective properties are passed as function parameter. The function realizing a derivation rule might either call other derivation rules or add properties to the given derivation.
 * 
 */
namespace smtrat::cadcells::operators::rules {

template<typename P>
void root_well_def(datastructures::SampledDerivation<P>& deriv, datastructures::IndexedRoot root) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "well_def(" << root << ", " << deriv.sample() << ")");
    assert(deriv.contains(properties::poly_pdel{ root.poly }));

    if (root.index != 1 && root.index != deriv.proj().num_roots(deriv.sample(), root.poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> well_def(" << root << ", " << deriv.sample() << ") <= proj_del(" << root.poly << ") && 0 < " << root << ".index < |real_roots(" << root.poly << "(" << deriv.sample() << "))|");
    } else if (deriv.proj().is_ldcf_zero(deriv.sample(), root.poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> well_def(" << root << ", " << deriv.sample() << ") <= proj_del(" << root.poly << ") && ldcf(" << root.poly << ")(" << deriv.sample() << ") = 0");
    } else {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> well_def(" << root << ", " << deriv.sample() << ") <= proj_del(" << root.poly << ") && sgn_inv(ldcf(" << root.poly << "))");
        deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(root.poly) });
    }
}

template<typename P>
bool is_trivial_root_well_def(datastructures::SampledDerivation<P>& deriv, datastructures::IndexedRoot root) {
    if (root.index != 1 && root.index != deriv.proj().num_roots(deriv.sample(), root.poly)) {
        return true;
    } else if (deriv.proj().is_ldcf_zero(deriv.sample(), root.poly)) {
        return true;
    } else {
        return false;
    }
}


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
            return carl::level_of(a) < carl::level_of(b) || (carl::level_of(a) == carl::level_of(b) && a.degree() < b.degree());
        });
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "non_null(" << poly << ") <= sgn_inv(" << coeff << ") && " << coeff << " in coeff(" << poly << ")");
        deriv.insert(properties::poly_sgn_inv{ coeff });
    }
    return true;
}

template<typename P>
bool poly_pdel(datastructures::SampledDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "proj_del(" << poly << ")");
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> proj_del(" << poly << ") <= non_null(" << poly << ") && ord_inv(disc(" << poly << ") [" << deriv.proj().disc(poly) << "]) && cell_connected(" << (poly.level-1) << ")");
    deriv.insert(properties::poly_ord_inv{ deriv.proj().disc(poly) });
    deriv.insert(properties::cell_connected{ poly.level-1 });
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
            SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv(" << poly << ") <= proj_del(" << poly << ") && sgn_inv(" << poly << ") && cell_connected(" << poly.level << ")");
            deriv.insert(properties::poly_pdel{ poly });
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
void poly_ord_inv_base(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& cell, const datastructures::IndexedRootOrdering& /*ordering*/, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "ord_inv_base(" << poly << "), " << poly << " irreducible");
    if (deriv.proj().is_const(poly)) return; 

    if (deriv.proj().is_zero(deriv.sample(), poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv_base(" << poly << ") <= proj_del(" << poly << ") && cell_connected(" << poly.level << ")");
        deriv.insert(properties::poly_pdel{ poly });
        deriv.insert(properties::cell_connected{ poly.level });
    } else if (cell.is_section() && !deriv.proj().is_zero(deriv.sample(), poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv_base(" << poly << ") <= " << poly << "(" << deriv.sample() << ") != 0 && holds(" << cell << ")");
    } else {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv_base(" << poly << ") <= proj_del(" << poly << ") && cell_connected(" << poly.level << ")");
        deriv.insert(properties::poly_pdel{ poly });
        deriv.insert(properties::cell_connected{ poly.level });
    }
}

template<typename P>
void poly_sgn_inv(datastructures::DelineatedDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "sgn_inv(" << poly << ")");
    if (deriv.proj().is_const(poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> sgn_inv(" << poly << ") <= " << poly << " const");
    } else if (deriv.contains(properties::poly_ord_inv{ poly })) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> sgn_inv(" << poly << ") <= ord_inv(" << poly << ")");
    } else {
        auto factors = deriv.proj().factors_nonconst(poly);
        for (const auto& factor : factors) {
            if (factor.level < poly.level && deriv.proj().is_zero(deriv.underlying_sample(), factor)) {
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> sgn_inv(" << poly << ") <= sgn_inv(" << factor << ") && "<< factor <<"("<< deriv.underlying_sample() <<")=0");
                deriv.insert(properties::poly_irreducible_sgn_inv{ factor });
                return;
            }
        }

        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> sgn_inv(" << poly << ") <= sgn_inv(factors(" << poly << ")) <=> sgn_inv(" << factors << ")");
        for (const auto& factor : factors) {
            deriv.insert(properties::poly_irreducible_sgn_inv{ factor });
        }
    }
}

template<typename P>
void poly_semi_sgn_inv(datastructures::DelineatedDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "semi_sgn_inv(" << poly << ")");
    if (deriv.proj().is_const(poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> semi_sgn_inv(" << poly << ") <= " << poly << " const");
    } else if (deriv.contains(properties::poly_ord_inv{ poly })) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> semi_sgn_inv(" << poly << ") <= ord_inv(" << poly << ")");
    } else if (deriv.contains(properties::poly_sgn_inv{ poly }) || deriv.contains(properties::poly_irreducible_sgn_inv{ poly })) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> semi_sgn_inv(" << poly << ") <= poly_sgn_inv(" << poly << ")");
    } else {
        auto factors = deriv.proj().factors_nonconst(poly);
        for (const auto& factor : factors) {
            if (factor.level < poly.level && deriv.proj().is_zero(deriv.underlying_sample(), factor)) {
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> semi_sgn_inv(" << poly << ") <= sgn_inv(" << factor << ") && "<< factor <<"("<< deriv.underlying_sample() <<")=0");
                deriv.insert(properties::poly_irreducible_sgn_inv{ factor });
                return;
            }
        }

        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> semi_sgn_inv(" << poly << ") <= semi_sgn_inv(factors(" << poly << ")) <=> semi_sgn_inv(" << factors << ")");
        for (const auto& factor : factors) {
            deriv.insert(properties::poly_irreducible_semi_sgn_inv{ factor });
        }
    }
}

template<typename P>
void poly_irreducible_nonzero_sgn_inv(datastructures::DelineatedDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "sgn_inv(" << poly << "), " << poly << " irreducible and non-zero");
    assert(deriv.proj().num_roots(deriv.underlying_sample(), poly) == 0);
    deriv.insert(properties::poly_pdel{ poly });
    if (deriv.proj().is_ldcf_zero(deriv.underlying_sample(), poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> sgn_inv(" << poly << ") <= proj_del(" << poly << ") && sgn_inv(ldcf(" << poly << ") [" << deriv.proj().ldcf(poly) << "])");
        deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) });
    } else {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> sgn_inv(" << poly << ") <= proj_del(" << poly << ")");
    }
}

template<typename P>
void poly_irreducible_nonzero_semi_sgn_inv(datastructures::DelineatedDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "semi_sgn_inv(" << poly << "), " << poly << " irreducible and non-zero");
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> semi_sgn_inv(" << poly << ") <= sgn_inv(" << poly << ")");
    poly_irreducible_nonzero_sgn_inv(deriv, poly);
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
    if (!cell.is_section() && !cell.lower().is_infty() && !cell.upper().is_infty() /*&& cell.lower().value().poly != cell.upper().value().poly*/) {
        // assert(deriv.contains(properties::poly_pdel{ cell.lower().value().poly }));
        // assert(deriv.contains(properties::poly_pdel{ cell.upper().value().poly }));
        assert(ordering.holds_transitive(cell.lower().value(),cell.upper().value(), false));
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
    assert(deriv.contains(properties::poly_pdel{ cell.section_defining().poly }));
    assert(deriv.contains(properties::poly_sgn_inv{ deriv.proj().ldcf(cell.section_defining().poly) }));
    deriv.insert(properties::cell_connected{ poly.level-1 });
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
void root_represents(datastructures::SampledDerivation<P>& deriv, datastructures::IndexedRoot root) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "ir_rep(" << root << ", " << deriv.sample() << ")");
    assert(deriv.contains(properties::poly_pdel{ root.poly }));
    deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(root.poly) });
}

template<typename P>
void cell_represents(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& cell) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "repr(" << cell << ")");
    if (!cell.is_section()) {
        if (!cell.lower().is_infty()) {
            if (cell.lower().value().is_root()) {
                root_represents(deriv, cell.lower().value().root());
            } else {
                for (const auto& root : cell.lower().value().roots()) {
                    root_represents(deriv, root);
                }
            }
        }
        if (!cell.upper().is_infty()) {
            if (cell.upper().value().is_root()) {
                root_represents(deriv, cell.upper().value().root());
            } else {
                for (const auto& root : cell.upper().value().roots()) {
                    root_represents(deriv, root);
                }
            }
        }
    } else {
        root_represents(deriv, cell.section_defining());
    }
}

template<typename P>
void root_ordering_holds(datastructures::SampledDerivation<P>& deriv, const datastructures::IndexedRootOrdering& ordering) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "ir_ord(" << ordering << ", " << deriv.sample() << ")");
    deriv.insert(properties::cell_connected{ deriv.level() });
    for (const auto& rel : ordering.data()) {
        assert(rel.first.is_root() && rel.second.is_root());
        auto& first = rel.first.root();
        auto& second = rel.second.root();
        if (first.poly != second.poly) {
            assert(rel.is_strict || (ordering.holds_transitive(first,second,false) && ordering.holds_transitive(second,first,false))); // not supported
            assert(deriv.contains(properties::poly_pdel{ first.poly }));
            assert(deriv.contains(properties::poly_pdel{ second.poly }));
            deriv.insert(properties::poly_ord_inv{ deriv.proj().res(first.poly, second.poly) });
        }
    }
}

namespace additional_root_outside_util {
    inline boost::container::flat_set<datastructures::PolyRef> resultant_polys(const datastructures::PolyRef& poly, const datastructures::IndexedRootOrdering& ordering) {
        boost::container::flat_set<datastructures::PolyRef> result;
        for (const auto& rel : ordering.data()) {
            if (rel.first.has_poly(poly)) {
                rel.second.polys(result);
            } else if (rel.second.has_poly(poly)) {
                rel.first.polys(result);
            }
        }
        return result;
    }

    template<typename P>
    inline std::optional<datastructures::IndexedRoot> protect_lower(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& cell, const datastructures::IndexedRootOrdering& ordering, const datastructures::PolyRef& poly, const boost::container::flat_set<datastructures::PolyRef>& res_polys, bool strict = false) {
        {
            auto ir = cell.lower().value().poly_root(poly);
            if (ir) return *ir;
        }

        auto lower_root = ordering.holds_transitive(poly, cell.lower().value(), strict);
        if (lower_root) {
            if (!lower_root->is_root()) {
                assert(false);
                return std::nullopt;
            } else if (deriv.contains(properties::root_well_def{lower_root->root()}) || is_trivial_root_well_def(deriv.underlying().sampled(), lower_root->root())) {
                return lower_root->root();
            }
        }

        // check if a res_poly has a well defined root below
        for (const auto& res_poly : res_polys) {
            auto ir = cell.lower().value().poly_root(res_poly);
            if (ir) return *ir;
            else {
                auto res_lower_root = ordering.holds_transitive(res_poly, cell.lower().value(), strict);
                if (res_lower_root) {
                    if (!res_lower_root->is_root()) {
                        assert(false);
                        return std::nullopt;
                    } else if (deriv.contains(properties::root_well_def{res_lower_root->root()}) || is_trivial_root_well_def(deriv.underlying().sampled(), res_lower_root->root())) {
                        return res_lower_root->root();
                    }
                }
            }
        }

        if (lower_root) return lower_root->root();
        return std::nullopt;
    }

    template<typename P>
    inline std::optional<datastructures::IndexedRoot> protect_upper(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& cell, const datastructures::IndexedRootOrdering& ordering, const datastructures::PolyRef& poly, const boost::container::flat_set<datastructures::PolyRef>& res_polys, bool strict = false) {
        {
            auto ir = cell.upper().value().poly_root(poly);
            if (ir) return *ir;
        }

        auto upper_root = ordering.holds_transitive(cell.upper().value(), poly, strict);
        if (upper_root) {
            if (!upper_root->is_root()) {
                assert(false);
                return std::nullopt;
            } else if (deriv.contains(properties::root_well_def{upper_root->root()}) || is_trivial_root_well_def(deriv.underlying().sampled(), upper_root->root())) {
                return upper_root->root();
            }
        }

        // check if a res_poly has a well defined root above
        for (const auto& res_poly : res_polys) {
            auto ir = cell.upper().value().poly_root(res_poly);
            if (ir) return *ir;
            else {
                auto res_upper_root = ordering.holds_transitive(cell.upper().value(), res_poly, strict);
                if (res_upper_root) {
                    if (!res_upper_root->is_root()) {
                        assert(false);
                        return std::nullopt;
                    } else if (deriv.contains(properties::root_well_def{res_upper_root->root()}) || is_trivial_root_well_def(deriv.underlying().sampled(), res_upper_root->root())) {
                        return res_upper_root->root();
                    }
                }
            }
        }

        if (upper_root) return upper_root->root();
        return std::nullopt;
    }
}

template<typename P>
void poly_additional_root_outside(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& cell, const datastructures::IndexedRootOrdering& ordering, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "additional_root_outside(" << poly << ")");
    assert(!deriv.proj().is_nullified(deriv.underlying_sample(), poly));
    assert(deriv.contains(properties::poly_pdel{ poly }));
    deriv.insert(properties::cell_connected{ poly.level-1 });

    if (deriv.contains(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) })) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ldcf already contained");
    } else if (cell.is_section() && deriv.proj().is_zero(deriv.sample(), poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> additional_root_outside(" << poly << ") <= connected(" << (poly.level-1) << ") && proj_del(" << poly << ") && repr(" << cell << ") && " << poly << "(" << deriv.sample() << ")=0 && ir_holds(" << ordering << ")");
        // ok by indexed root ordering!
    } else {
        // assert(!deriv.proj().is_zero(deriv.sample(), poly)); 
        if (!cell.is_section() && (cell.lower().is_infty() || cell.upper().is_infty())) {
            deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) });
            SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> additional_root_outside(" << poly << ") <= connected(" << (poly.level-1) << ") && proj_del(" << poly << ") && sgn_inv(ldcf(" << poly << ") [" << deriv.proj().ldcf(poly) << "])");
        } else {
            // compute set of polynomials that have a resultant with the current polynomials (according to the given ordering)
            boost::container::flat_set<datastructures::PolyRef> res_polys = additional_root_outside_util::resultant_polys(poly, ordering);
            
            auto lower = additional_root_outside_util::protect_lower(deriv, cell, ordering, poly, res_polys, false);
            auto upper = additional_root_outside_util::protect_upper(deriv, cell, ordering, poly, res_polys, false);
            
            if (!lower || !upper) {
                deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) });
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> additional_root_outside(" << poly << ") <= connected(" << (poly.level-1) << ") && proj_del(" << poly << ") && sgn_inv(ldcf(" << poly << ") [" << deriv.proj().ldcf(poly) << "])");
            } else {
                if (lower->poly != poly) {
                    //assert(deriv.contains(properties::poly_ord_inv{ deriv.proj().res(lower->poly, poly) }));
                    //deriv.insert(properties::poly_ord_inv{ deriv.proj().res(lower->poly, poly) });
                    if (!deriv.contains(properties::poly_ord_inv{ deriv.proj().res(lower->poly, poly) })) {
                        deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) });
                        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> additional_root_outside(" << poly << ") <= connected(" << (poly.level-1) << ") && proj_del(" << poly << ") && sgn_inv(ldcf(" << poly << ") [" << deriv.proj().ldcf(poly) << "])");
                    } else {
                        deriv.insert(properties::root_well_def{*lower});
                        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> additional_root_outside(" << poly << ") <= connected(" << (poly.level-1) << ") && proj_del(" << poly << ") && well_def(" << *lower << ") && ord_inv(res(" << poly << ", "<< lower->poly <<") [" << deriv.proj().res(lower->poly, poly) << "]) && ir_holds(" << ordering << ")");
                    }
                } else {
                    deriv.insert(properties::root_well_def{*lower});
                    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> additional_root_outside(" << poly << ") <= connected(" << (poly.level-1) << ") && proj_del(" << poly << ") && well_def(" << *lower << ") && ir_holds(" << ordering << ")");
                }
                
                if (upper->poly != poly) {
                    //assert(deriv.contains(properties::poly_ord_inv{ deriv.proj().res(upper->poly, poly) }));
                    //deriv.insert(properties::poly_ord_inv{ deriv.proj().res(upper->poly, poly) });
                    if (!deriv.contains(properties::poly_ord_inv{ deriv.proj().res(upper->poly, poly) })) {
                        deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) });
                        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> additional_root_outside(" << poly << ") <= connected(" << (poly.level-1) << ") && proj_del(" << poly << ") && sgn_inv(ldcf(" << poly << ") [" << deriv.proj().ldcf(poly) << "])");
                    } else {
                        deriv.insert(properties::root_well_def{*upper});
                        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> additional_root_outside(" << poly << ") <= connected(" << (poly.level-1) << ") && proj_del(" << poly << ") && well_def(" << *upper << ") && ord_inv(res(" << poly << ", "<< upper->poly <<") [" << deriv.proj().res(upper->poly, poly) << "]) && ir_holds(" << ordering << ")");
                    }
                } else {
                    deriv.insert(properties::root_well_def{*upper});
                    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> additional_root_outside(" << poly << ") <= connected(" << (poly.level-1) << ") && proj_del(" << poly << ") && well_def(" << *upper << ") && ir_holds(" << ordering << ")");
                }
            }
        }
    }
}

template<typename P>
void poly_irreducible_sgn_inv(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& cell, const datastructures::IndexedRootOrdering& ordering, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "sgn_inv(" << poly << "), " << poly << " irreducible");
    poly_additional_root_outside(deriv, cell, ordering, poly);
}

template<typename P>
void poly_irreducible_semi_sgn_inv(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& cell, const datastructures::IndexedRootOrdering& ordering, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "semi_sgn_inv(" << poly << "), " << poly << " irreducible");
    poly_additional_root_outside(deriv, cell, ordering, poly);
}

template<typename P>
void poly_irreducible_sgn_inv_filtered(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& /*cell*/, const datastructures::IndexedRootOrdering& /*ordering*/, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "sgn_inv(" << poly << "), " << poly << " irreducible");
    deriv.insert(properties::poly_additional_root_outside{ poly });
}

template<typename P>
void poly_irreducible_semi_sgn_inv_filtered(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& /*cell*/, const datastructures::IndexedRootOrdering& /*ordering*/, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "semi_sgn_inv(" << poly << "), " << poly << " irreducible");
    deriv.insert(properties::poly_additional_root_outside{ poly });
}

}

#include "rules_ordering.h"
#include "rules_covering.h"