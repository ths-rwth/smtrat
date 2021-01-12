#pragma once

#include "properties.h"

namespace smtrat::cadcells::operators::rules {

void root_well_def(cell_derivation& deriv, indexed_root root) {
    assert(deriv.contains(properties::poly_pdel{ root.poly }));

    if (root.idx != 1 && idx != deriv.proj().num_roots(deriv.sample(), root.poly)) return;
    else if (!deriv.proj().is_ldcf_zero(deriv.sample(), root.poly)) return;
    else {
        deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(root.poly) });
    }
}

void poly_non_null(cell_derivation& deriv, datastructures::poly_ref poly) {
    assert(!deriv.proj().is_nullified(deriv.sample(), poly));

    if (deriv.proj().has_const_coeff(poly)) return;
    if (!deriv.proj().is_ldcf_zero(deriv.sample(), poly) && deriv.contains(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) } )) return;
    if (deriv.proj().know_disc(poly)) {
        if (!deriv.proj().is_disc_zero(deriv.sample(), poly) && deriv.contains(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) } )) return;
    }
    auto coeff = deriv.proj().simplest_nonzero_coeff(deriv.sample(), poly, [&](const Poly& a, const Poly& b) { // TODO:
        if (deriv.proj().known(a) && deriv.contains( properties::poly_sgn_inv { m_pool(a)} )) return true;
        if (deriv.proj().known(b) && deriv.contains( properties::poly_sgn_inv { m_pool(b)} )) return true;
        return datastructures::level_of(a) < datastructures::level_of(b) || (datastructures::level_of(a) == datastructures::level_of(b) && a.degree() < b.degree());
    });
    deriv.insert(properties::poly_sgn_inv{ coeff });
}

void poly_pdel(cell_derivation& deriv, datastructures::poly_ref poly) {
    poly_non_null(deriv, poly);
    deriv.insert(properties::poly_ord_inv{ deriv.proj().disc(poly) });
}

void poly_irrecubile_ord_inv(cell_derivation& deriv, datastructures::poly_ref poly) {
    if (deriv.proj().is_const(prop.poly)) return;
    
    deriv.insert(properties::poly_irreducible_sgn_inv{ poly });
    if (deriv.proj().is_zero(deriv.sample(), poly)) {
        deriv.insert(properties::poly_pdel{ poly });
    }
}

void poly_ord_inv(cell_derivation& deriv, datastructures::poly_ref poly) {
    if (deriv.proj().is_const(prop.poly)) return;

    auto factors = deriv.proj().factors_nonconst(poly);
    for (const auto& factor : factors) {
        poly_irrecubile_ord_inv(deriv, factor);
    }
}

void poly_sgn_inv(derivation& deriv, datastructures::poly_ref poly) {
    if (deriv.proj().is_const(prop.poly)) return;

    if (deriv.contains(properties::poly_ord_inv{ poly })) return;
    else {
        auto factors = deriv.proj().factors_nonconst(poly);
        for (const auto& factor : factors) {
            deriv.insert(properties::poly_irreducible_sgn_inv{ poly });
        }
    }
}

void poly_irrecubile_nonzero_sgn_inv(derivation& deriv, datastructures::poly_ref poly) {
    assert(deriv.contains(properties::poly_pdel{ poly }));
    assert(deriv.proj().num_roots(deriv.underlying_sample(), poly) == 0);
    if (deriv.proj().is_ldcf_zero(deriv.underlying_sample(), poly)) {
        deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) });
    }
}

void cell_connected(cell_derivation& deriv, const cell& representative) {
    if (representative.is_sector() && representative.lower() && representative.upper() && representative.lower()->poly != representative.upper()->poly) {
        assert(deriv.contains(properties::poly_pdel{ representative.lower()->poly }));
        assert(deriv.contains(properties::poly_pdel{ representative.upper()->poly }));
        deriv.insert(properties::poly_ord_inv{ deriv.proj().res(representative.lower()->poly, representative.upper()->poly) });
    }
}

void cell_analytic_submanifold(cell_derivation& deriv, const cell& representative) {
}

void poly_irrecubile_sgn_inv_ec(cell_derivation& deriv, const cell& representative, datastructures::poly_ref poly) {
    assert(representative.is_section());
    assert(deriv.contains(properties::poly_pdel{ representative.sector_defining().poly }));
    assert(deriv.contains(properties::poly_sgn_inv{ deriv.proj().ldcf(representative.sector_defining().poly) }));
    if (representative.sector_defining().poly != poly) {
        deriv.insert(properties::poly_ord_inv{ deriv.proj().res(representative.sector_defining().poly, poly) });
    }
}

void root_represents(cell_derivation& deriv, indexed_root root) {
    assert(deriv.contains(properties::poly_pdel{ root.poly }));
    deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(root.poly) });
}

void cell_represents(cell_derivation& deriv, const cell& representative) {
    if (representative.lower()) {
        root_represents(deriv, *representative.lower());
    }
    if (representative.upper()) {
        root_represents(deriv, *representative.upper());
    }
}

void root_ordering_holds(cell_derivation& deriv, const cell& representative, const indexed_root_ordering& ordering) {
    for (const auto& rel : ordering.data_below()) {
        if (rel.first.poly != rel.second.poly) {
            assert(deriv.contains(properties::poly_pdel{ rel.first.poly }));
            assert(deriv.contains(properties::poly_pdel{ rel.second.poly }));
            deriv.insert(properties::poly_ord_inv{ deriv.proj().res(rel.first.poly, rel.second.poly) });
            deriv.insert(properties::root_well_def{ rel.first });
        }
    }
    for (const auto& rel : ordering.data_above()) {
        if (rel.first.poly != rel.second.poly) {
            assert(deriv.contains(properties::poly_pdel{ rel.first.poly }));
            assert(deriv.contains(properties::poly_pdel{ rel.second.poly }));
            deriv.insert(properties::poly_ord_inv{ deriv.proj().res(rel.first.poly, rel.second.poly) });
            deriv.insert(properties::root_well_def{ rel.first });
        }
    }
}

void poly_irrecubile_sgn_inv(cell_derivation& deriv, const cell& representative, const indexed_root_ordering& ordering, datastructures::poly_ref poly) {
    assert(deriv.contains(properties::poly_pdel{ poly }));
    if (representative.is_section() && deriv.proj().is_zero(sample, poly)) {
        auto roots = deriv.proj().real_roots(poly);
        auto it = std::find(roots.begin(), roots.end(), sample);
        deriv.insert(properties::root_well_def{ poly, std::distance(roots.begin(), it) + 1 });
    } else {
        assert(!deriv.proj().is_zero(sample, poly));
        if (representative.is_sector() && (del.lower_unbounded() || del.upper_unbounded())) {
            deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) });
        } else {
            bool has_lower = (poly == representative.lower().poly) || std::find_if(ordering.below().begin(), ordering.below().end(), [&poly](const auto& rel) { return rel.second.poly == poly }) != ordering.below().end();
            bool has_upper = (poly == representative.upper().poly) || std::find_if(ordering.above().begin(), ordering.above().end(), [&poly](const auto& rel) { return rel.second.poly == poly }) != ordering.above().end();
            if (!(has_lower && has_upper)) {
                // TODO implement further checks
                deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) });
            }
        }
    }
}

// TODO defer computation of resultants to next level

}