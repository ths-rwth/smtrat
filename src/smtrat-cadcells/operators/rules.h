#pragma once

#include "properties.h"
#include "../datastructures/derivation.h"

namespace smtrat::cadcells::operators::rules {

template<typename P>
void root_well_def(datastructures::sampled_derivation<P>& deriv, datastructures::indexed_root root) {
    assert(deriv.contains(properties::poly_pdel{ root.poly }));

    if (root.index != 1 && root.index != deriv.proj().num_roots(deriv.sample(), root.poly)) return;
    else if (!deriv.proj().is_ldcf_zero(deriv.sample(), root.poly)) return;
    else {
        deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(root.poly) });
    }
}

template<typename P>
void poly_non_null(datastructures::sampled_derivation<P>& deriv, datastructures::poly_ref poly) {
    assert(!deriv.proj().is_nullified(deriv.sample(), poly));

    if (deriv.proj().has_const_coeff(poly)) return;
    if (!deriv.proj().is_ldcf_zero(deriv.sample(), poly) && deriv.contains(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) } )) return;
    if (deriv.proj().know_disc(poly)) {
        if (!deriv.proj().is_disc_zero(deriv.sample(), poly) && deriv.contains(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) } )) return;
    }
    auto coeff = deriv.proj().simplest_nonzero_coeff(deriv.sample(), poly, [&](const Poly& a, const Poly& b) {
        if (deriv.proj().known(a) && deriv.contains( properties::poly_sgn_inv { deriv.proj().polys()(a)} )) return true;
        if (deriv.proj().known(b) && deriv.contains( properties::poly_sgn_inv { deriv.proj().polys()(b)} )) return true;
        return helper::level_of(deriv.polys().var_order(),a) < helper::level_of(deriv.polys().var_order(),b) || (helper::level_of(deriv.polys().var_order(),a) == helper::level_of(deriv.polys().var_order(),b) && a.degree(helper::main_var(deriv.polys().var_order(), a)) < b.degree(helper::main_var(deriv.polys().var_order(), b)));
    });
    deriv.insert(properties::poly_sgn_inv{ coeff });
}

template<typename P>
void poly_pdel(datastructures::sampled_derivation<P>& deriv, datastructures::poly_ref poly) {
    poly_non_null(deriv, poly);
    deriv.insert(properties::poly_ord_inv{ deriv.proj().disc(poly) });
}

template<typename P>
void poly_irrecubile_ord_inv(datastructures::sampled_derivation<P>& deriv, datastructures::poly_ref poly) {
    if (deriv.proj().is_const(poly)) return;
    
    deriv.insert(properties::poly_irreducible_sgn_inv{ poly });
    if (deriv.proj().is_zero(deriv.sample(), poly)) {
        deriv.insert(properties::poly_pdel{ poly });
    }
}

template<typename P>
void poly_ord_inv(datastructures::sampled_derivation<P>& deriv, datastructures::poly_ref poly) {
    if (deriv.proj().is_const(poly)) return;

    auto factors = deriv.proj().factors_nonconst(poly);
    for (const auto& factor : factors) {
        poly_irrecubile_ord_inv(deriv, factor);
    }
}

template<typename P>
void poly_sgn_inv(datastructures::base_derivation<P>& deriv, datastructures::poly_ref poly) {
    if (deriv.proj().is_const(poly)) return;

    if (deriv.contains(properties::poly_ord_inv{ poly })) return;
    else {
        auto factors = deriv.proj().factors_nonconst(poly);
        for (const auto& factor : factors) {
            deriv.insert(properties::poly_irreducible_sgn_inv{ poly });
        }
    }
}

template<typename P>
void poly_irrecubile_nonzero_sgn_inv(datastructures::base_derivation<P>& deriv, datastructures::poly_ref poly) {
    assert(deriv.contains(properties::poly_pdel{ poly }));
    assert(deriv.proj().num_roots(deriv.underlying_sample(), poly) == 0);
    if (deriv.proj().is_ldcf_zero(deriv.underlying_sample(), poly)) {
        deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) });
    }
}

template<typename P>
void cell_connected(datastructures::sampled_derivation<P>& deriv, const datastructures::cell& representative) {
    if (representative.is_sector() && representative.lower() && representative.upper() && representative.lower()->poly != representative.upper()->poly) {
        assert(deriv.contains(properties::poly_pdel{ representative.lower()->poly }));
        assert(deriv.contains(properties::poly_pdel{ representative.upper()->poly }));
        deriv.insert(properties::poly_ord_inv{ deriv.proj().res(representative.lower()->poly, representative.upper()->poly) });
    }
}

template<typename P>
void cell_analytic_submanifold(datastructures::sampled_derivation<P>& deriv, const datastructures::cell& representative) {
}

template<typename P>
void poly_irrecubile_sgn_inv_ec(datastructures::sampled_derivation<P>& deriv, const datastructures::cell& representative, datastructures::poly_ref poly) {
    assert(representative.is_section());
    assert(deriv.contains(properties::poly_pdel{ representative.sector_defining().poly }));
    assert(deriv.contains(properties::poly_sgn_inv{ deriv.proj().ldcf(representative.sector_defining().poly) }));
    if (representative.sector_defining().poly != poly) {
        deriv.insert(properties::poly_ord_inv{ deriv.proj().res(representative.sector_defining().poly, poly) });
    }
}

template<typename P>
void root_represents(datastructures::sampled_derivation<P>& deriv, datastructures::indexed_root root) {
    assert(deriv.contains(properties::poly_pdel{ root.poly }));
    deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(root.poly) });
}

template<typename P>
void cell_represents(datastructures::sampled_derivation<P>& deriv, const datastructures::cell& representative) {
    if (representative.lower()) {
        root_represents(deriv, *representative.lower());
    }
    if (representative.upper()) {
        root_represents(deriv, *representative.upper());
    }
}

template<typename P>
void root_ordering_holds(datastructures::sampled_derivation<P>& deriv, const datastructures::cell& representative, const datastructures::indexed_root_ordering& ordering) {
    for (const auto& rel : ordering.below()) {
        if (rel.first.poly != rel.second.poly) {
            assert(deriv.contains(properties::poly_pdel{ rel.first.poly }));
            assert(deriv.contains(properties::poly_pdel{ rel.second.poly }));
            deriv.insert(properties::poly_ord_inv{ deriv.proj().res(rel.first.poly, rel.second.poly) });
            deriv.insert(properties::root_well_def{ rel.first });
        }
    }
    for (const auto& rel : ordering.above()) {
        if (rel.first.poly != rel.second.poly) {
            assert(deriv.contains(properties::poly_pdel{ rel.first.poly }));
            assert(deriv.contains(properties::poly_pdel{ rel.second.poly }));
            deriv.insert(properties::poly_ord_inv{ deriv.proj().res(rel.first.poly, rel.second.poly) });
            deriv.insert(properties::root_well_def{ rel.first });
        }
    }
}

template<typename P>
void poly_irrecubile_sgn_inv(datastructures::sampled_derivation<P>& deriv, const datastructures::cell& representative, const datastructures::indexed_root_ordering& ordering, datastructures::poly_ref poly) {
    assert(deriv.contains(properties::poly_pdel{ poly }));
    if (representative.is_section() && deriv.proj().is_zero(deriv.sample(), poly)) {
        auto roots = deriv.proj().real_roots(deriv.sample(), poly);
        auto it = std::find(roots.begin(), roots.end(), deriv.sample());
        deriv.insert(properties::root_well_def{ poly, std::distance(roots.begin(), it) + 1 });
    } else {
        assert(!deriv.proj().is_zero(deriv.sample(), poly));
        if (representative.is_sector() && (deriv.cell().lower_unbounded() || deriv.cell().upper_unbounded())) {
            deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) });
        } else {
            bool has_lower = (poly == representative.lower()->poly) || std::find_if(ordering.below().begin(), ordering.below().end(), [&poly](const auto& rel) { return rel.second.poly == poly; }) != ordering.below().end();
            bool has_upper = (poly == representative.upper()->poly) || std::find_if(ordering.above().begin(), ordering.above().end(), [&poly](const auto& rel) { return rel.second.poly == poly; }) != ordering.above().end();
            if (!(has_lower && has_upper)) {
                // TODO later: implement further checks
                deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) });
            }
        }
    }
}

template<typename P>
void covering_holds(datastructures::base_derivation<P>& deriv, const datastructures::covering& covering) {
    for (auto it = covering.cells().begin(); it != covering.cells().end()-1; it++) {
        assert(deriv.contains(properties::root_well_def{ it->upper() }));
        assert(deriv.contains(properties::root_well_def{ std::next(it)->lower() }));
        if (it->upper()->poly != std::next(it)->lower()->poly) {
            deriv.insert(properties::poly_ord_inv{ deriv.proj().res(it->upper()->poly, std::next(it)->lower()->poly) });
        }
    }
}

}