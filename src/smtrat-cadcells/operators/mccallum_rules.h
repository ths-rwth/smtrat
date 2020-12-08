#pragma once

#include "mccallum_properties.h"

namespace smtrat::cadcells::operators::mccallum::rules {

void root_well_def(datastructures::projections& proj, properties::properties& props, const Model& sample, datastructures::poly_ref poly, size_t idx) {
    assert(props.contains(properties::poly_pdel{ poly }));

    if (idx != 1 && idx != proj.num_roots(sample, poly)) return;
    else if (!proj.is_ldcf_zero(sample, poly)) return;
    else {
        props.insert(properties::poly_sgn_inv{ proj.ldcf(poly) });
    }
}

void poly_non_null(datastructures::projections& proj, properties::properties& props, const Model& sample, datastructures::poly_ref poly) {
    assert(!proj.is_nullified(sample, poly));

    if (proj.has_const_coeff(poly)) return;
    if (!proj.is_ldcf_zero(sample, poly) && props.contains(properties::poly_sgn_inv{ proj.ldcf(poly) } )) return;
    if (proj.know_disc(poly)) {
        if (!proj.is_disc_zero(sample, poly) && props.contains(properties::poly_sgn_inv{ proj.ldcf(poly) } )) return;
    }
    auto coeff = proj.simplest_nonzero_coeff(sample, poly, [&](const Poly& a, const Poly& b) { // TODO:
        if (proj.known(a) && props.contains( properties::poly_sgn_inv { m_pool(a)} )) return true;
        if (proj.known(b) && props.contains( properties::poly_sgn_inv { m_pool(b)} )) return true;
        return level_of(a) < level_of(b) || (level_of(a) == level_of(b) && a.degree() < b.degree());
    });
    props.insert(properties::poly_sgn_inv{ coeff });
}

void poly_pdel(datastructures::projections& proj, properties::properties& props, const Model& sample, datastructures::poly_ref poly) {
    poly_non_null(proj, props, sample, poly);
    props.insert(properties::poly_ord_inv{ proj.disc(poly) });
}

void poly_irrecubile_ord_inv(datastructures::projections& proj, properties::properties& props, const Model& sample, datastructures::poly_ref poly) {
    props.insert(properties::poly_irreducible_sgn_inv{ poly });
    if (proj.is_zero(sample, poly)) {
        props.insert(properties::poly_pdel{ poly });
    }
}

void poly_ord_inv(datastructures::projections& proj, properties::properties& props, const Model& sample, datastructures::poly_ref poly) {
    auto factors = proj.factors_nonconst(poly);
    for (const auto& factor : factors) {
        poly_irrecubile_ord_inv(proj, props, sample, factor);
    }
}

void poly_sgn_inv(datastructures::projections& proj, properties::properties& props, const Model& sample, datastructures::poly_ref poly) {
    if (props.contains(properties::poly_ord_inv{ poly })) return;
    else {
        auto factors = proj.factors_nonconst(poly);
        for (const auto& factor : factors) {
            props.insert(properties::poly_irreducible_sgn_inv{ poly });
        }
    }
}

// TODO defer computation of resultants to next level

// TODO add pseudo rules from paper

}