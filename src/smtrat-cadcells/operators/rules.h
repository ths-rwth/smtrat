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
    }
    else if (deriv.proj().is_ldcf_zero(deriv.sample(), root.poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> well_def(" << root << ", " << deriv.sample() << ") <= proj_del(" << root.poly << ") && ldcf(" << root.poly << ")(" << deriv.sample() << ") = 0");
    }
    else {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> well_def(" << root << ", " << deriv.sample() << ") <= proj_del(" << root.poly << ") && sgn_inv(ldcf(" << root.poly << "))");
        deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(root.poly) });
    }
}

template<typename P>
bool is_trivial_root_well_def(datastructures::SampledDerivation<P>& deriv, datastructures::IndexedRoot root) {
    if (root.index != 1 && root.index != deriv.proj().num_roots(deriv.sample(), root.poly)) {
        return true;
    }
    else if (deriv.proj().is_ldcf_zero(deriv.sample(), root.poly)) {
        return true;
    }
    else {
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
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "non_null(" << poly << ") <= ldcf(" << poly << ")(" << deriv.sample() << ")!=0 && sgn_inv(ldcf(" << poly << "))");
    } else if (
        deriv.proj().know_disc(poly) && !deriv.proj().is_disc_zero(deriv.sample(), poly) &&
        (deriv.contains(properties::poly_sgn_inv{ deriv.proj().disc(poly) }) || deriv.contains(properties::poly_ord_inv{ deriv.proj().disc(poly) }))
    ) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "non_null(" << poly << ") <= disc(" << poly << ")(" << deriv.sample() << ")!=0 && sgn_inv(disc(" << poly << "))");
    } else {
        auto coeff = deriv.proj().simplest_nonzero_coeff(deriv.sample(), poly, [&](const Poly& a, const Poly& b) {
            if (deriv.proj().known(a) && deriv.contains( properties::poly_sgn_inv { deriv.proj().polys()(a)} )) return true;
            if (deriv.proj().known(b) && deriv.contains( properties::poly_sgn_inv { deriv.proj().polys()(b)} )) return true;
            return helper::level_of(deriv.polys().var_order(),a) < helper::level_of(deriv.polys().var_order(),b) || (helper::level_of(deriv.polys().var_order(),a) == helper::level_of(deriv.polys().var_order(),b) && a.degree(helper::main_var(deriv.polys().var_order(), a)) < b.degree(helper::main_var(deriv.polys().var_order(), b)));
        });
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "non_null(" << poly << ") <= sgn_inv(" << coeff << ") && " << coeff << " is coeff of " << poly << "");
        deriv.insert(properties::poly_sgn_inv{ coeff });
    }
    return true;
}

template<typename P>
bool poly_pdel(datastructures::SampledDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "proj_del(" << poly << ")");
    if (!poly_non_null(deriv, poly)) return false;
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> proj_del(" << poly << ") <= non_null(" << poly << ") && ord_inv(disc(" << poly <<"))");
    deriv.insert(properties::poly_ord_inv{ deriv.proj().disc(poly) });
    deriv.insert(properties::cell_connected{ poly.level-1 });
    return true;
}

template<typename P>
void poly_irrecubile_ord_inv(datastructures::SampledDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "ord_inv(" << poly << "), " << poly << " irreducible");
    if (deriv.proj().is_const(poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv(" << poly << ") <= " << poly << " const");
    } else {
        if (deriv.proj().is_zero(deriv.sample(), poly)) {
            SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv(" << poly << ") <= proj_del(" << poly << ") && sgn_inv(" << poly << ")");
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
            poly_irrecubile_ord_inv(deriv, factor);
        }
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
void poly_irrecubile_nonzero_sgn_inv(datastructures::DelineatedDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "sgn_inv(" << poly << "), " << poly << " irreducible and non-zero");
    assert(deriv.proj().num_roots(deriv.underlying_sample(), poly) == 0);
    deriv.insert(properties::poly_pdel{ poly });
    if (deriv.proj().is_ldcf_zero(deriv.underlying_sample(), poly)) {
        deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) });
    }
}

template<typename P>
void cell_connected(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& cell, const datastructures::IndexedRootOrdering& ordering) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "connected(" << deriv.level() << ")");
    if (!cell.is_section() && !cell.lower().is_infty() && !cell.upper().is_infty() && cell.lower().value().poly != cell.upper().value().poly) {
        assert(deriv.contains(properties::poly_pdel{ cell.lower().value().poly }));
        assert(deriv.contains(properties::poly_pdel{ cell.upper().value().poly }));
        assert(ordering.leq_transitive(cell.lower().value(),cell.upper().value()));
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
    assert(deriv.proj().is_nullified(deriv.underlying_sample(), poly));
    assert(deriv.contains(properties::poly_pdel{ cell.section_defining().poly }));
    assert(deriv.contains(properties::poly_sgn_inv{ deriv.proj().ldcf(cell.section_defining().poly) }));
    deriv.insert(properties::cell_connected{ poly.level-1 });
    if (cell.section_defining().poly != poly) {
        deriv.insert(properties::poly_ord_inv{ deriv.proj().res(cell.section_defining().poly, poly) });
    }
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
            root_represents(deriv, cell.lower().value());
        }
        if (!cell.upper().is_infty()) {
            root_represents(deriv, cell.upper().value());
        }
    } else {
        root_represents(deriv, cell.section_defining());
    }
}

template<typename P>
void cell_well_def(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& cell) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "well_def(" << cell << ")");
    if (!cell.is_section()) {
        if (!cell.lower().is_infty()) {
            deriv.insert(properties::root_well_def{ cell.lower().value() });
        }
        if (!cell.upper().is_infty()) {
            deriv.insert(properties::root_well_def{ cell.upper().value() });
        }
    } else {
        deriv.insert(properties::root_well_def{ cell.section_defining() });
    }
}

template<typename P>
void root_ordering_holds(datastructures::SampledDerivation<P>& deriv, const datastructures::IndexedRootOrdering& ordering) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "ir_ord(" << ordering << ", " << deriv.sample() << ")");
    deriv.insert(properties::cell_connected{ deriv.level() });
    for (const auto& rel : ordering.data()) {
        if (rel.first.poly != rel.second.poly) {
            assert(deriv.contains(properties::poly_pdel{ rel.first.poly }));
            assert(deriv.contains(properties::poly_pdel{ rel.second.poly }));
            deriv.insert(properties::poly_ord_inv{ deriv.proj().res(rel.first.poly, rel.second.poly) });
        }
    }
}

template<typename P>
void poly_irreducible_sgn_inv(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& cell, const datastructures::IndexedRootOrdering& ordering, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "sgn_inv(" << poly << "), " << poly << " irreducible");
    assert(!deriv.proj().is_nullified(deriv.underlying_sample(), poly));
    assert(deriv.contains(properties::poly_pdel{ poly }));
    deriv.insert(properties::cell_connected{ poly.level-1 });
    if (cell.is_section() && deriv.proj().is_zero(deriv.sample(), poly)) {
        // ok by indexed root ordering!
    } else {
        assert(!deriv.proj().is_zero(deriv.sample(), poly));
        if (!cell.is_section() && (cell.lower().is_infty() || cell.upper().is_infty())) {
            deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) });
        } else {
            assert(cell.is_section() || (cell.lower().is_strict() && cell.upper().is_strict()));
            auto lower_root = ordering.leq_transitive(poly, cell.lower().value());
            auto upper_root = ordering.leq_transitive(cell.upper().value(), poly);

            // compute set of polynomials that have a resultant with the current polynomials (according to the given ordering)
            boost::container::flat_set<datastructures::PolyRef> res_polys;
            for (const auto& rel : ordering.data()) {
                if (rel.first.poly == poly) {
                    res_polys.insert(rel.second.poly);
                } else if (rel.second.poly == poly) {
                    res_polys.insert(rel.first.poly);
                }
            }
            
            // compute protection for lower bound
            auto protect_lower = [&]() {
                if (poly == cell.lower().value().poly) return true;

                if (upper_root) {
                    // check if a res_poly has a well defined root below
                    for (const auto& res_poly : res_polys) {
                        if (res_poly == cell.lower().value().poly) {
                            return true;
                        } else {
                            auto res_lower_root = ordering.leq_transitive(res_poly, cell.lower().value());
                            if (res_lower_root) {
                                if (deriv.contains(properties::root_well_def{*res_lower_root}) || is_trivial_root_well_def(deriv.underlying().sampled(), *res_lower_root)) {
                                    return true;
                                }
                            }
                        }
                    }
                }

                if (lower_root) {
                    deriv.insert(properties::root_well_def{*lower_root});
                    return true;
                }

                return false;
            };

            // compute protection for upper bound
            auto protect_upper = [&]() {
                if (poly == cell.upper().value().poly) return true;

                if (lower_root) {
                    // check if a res_poly has a well defined root above
                    for (const auto& res_poly : res_polys) {
                        if (res_poly == cell.upper().value().poly) {
                            return true;
                        } else {
                            auto res_upper_root = ordering.leq_transitive(cell.upper().value(), res_poly);
                            if (res_upper_root) {
                                if (deriv.contains(properties::root_well_def{*res_upper_root}) || is_trivial_root_well_def(deriv.underlying().sampled(), *res_upper_root)) {
                                    return true;
                                }
                            }
                        }
                    }
                }

                if (upper_root) {
                    deriv.insert(properties::root_well_def{*upper_root});
                    return true;
                }

                return false;
            };
            
            if (!protect_lower() || !protect_upper()) {
                deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) });
            }
        }
    }
}

template<typename P>
void poly_irreducible_sgn_inv(datastructures::DelineatedDerivation<P>& deriv, const datastructures::IndexedRootOrdering& /*ordering*/, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "sgn_inv(" << poly << "), " << poly << " irreducible");
    assert(deriv.contains(properties::poly_pdel{ poly }));
    assert(deriv.contains(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) }));
    // guaranteed by ordering
}

template<typename P>
void covering_holds(datastructures::DelineatedDerivation<P>& deriv, const datastructures::CoveringDescription& covering, const datastructures::IndexedRootOrdering& ordering) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "holds(" << covering << ")");
    for (auto it = covering.cells().begin(); it != covering.cells().end()-1; it++) {
        assert(deriv.contains(properties::root_well_def{ it->upper().value() }));
        assert(deriv.contains(properties::root_well_def{ std::next(it)->lower().value() }));
        assert(ordering.leq_transitive(std::next(it)->lower().value(), it->upper().value()));
    }
}

}