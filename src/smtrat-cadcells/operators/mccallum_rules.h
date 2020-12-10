#pragma once

#include "mccallum_properties.h"

namespace smtrat::cadcells::operators::mccallum::rules {

void root_well_def(datastructures::projections& proj, properties::properties& props, const Model& sample, indexed_root root) {
    assert(props.contains(properties::poly_pdel{ root.poly }));

    if (root.idx != 1 && idx != proj.num_roots(sample, root.poly)) return;
    else if (!proj.is_ldcf_zero(sample, root.poly)) return;
    else {
        props.insert(properties::poly_sgn_inv{ proj.ldcf(root.poly) });
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
        return datastructures::level_of(a) < datastructures::level_of(b) || (datastructures::level_of(a) == datastructures::level_of(b) && a.degree() < b.degree());
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


void poly_irrecubile_nonzero_sgn_inv(datastructures::projections& proj, properties::properties& props, const Model& sample, datastructures::poly_ref poly) {
    assert(props.contains(properties::poly_pdel{ poly }));
    assert(proj.num_roots(sample, poly) == 0);
    if (proj.is_ldcf_zero(sample, poly)) {
        props.insert(properties::poly_sgn_inv{ proj.ldcf(poly) });
    }
}

void cell_analytic_submanifold(datastructures::projections& proj, properties::properties& props, const Model& sample, const cell_at_level& representative) {
}

void poly_irrecubile_sgn_inv_ec(datastructures::projections& proj, properties::properties& props, const Model& sample, const cell_at_level& representative, datastructures::poly_ref poly) {
    assert(representative.is_section());
    assert(props.contains(properties::poly_pdel{ representative.sector_defining().poly }));
    assert(props.contains(properties::poly_sgn_inv{ proj.ldcf(representative.sector_defining().poly) }));
    if (representative.sector_defining().poly != poly) {
        props.insert(properties::poly_ord_inv{ proj.res(representative.sector_defining().poly, poly) });
    }
}

// TODO ir_ord

// TODO sgn_inv (def 2.17, 2.18)

void root_represents(datastructures::projections& proj, properties::properties& props, const Model& sample, indexed_root root) {
    assert(props.contains(properties::poly_pdel{ root.poly }));
    props.insert(properties::poly_sgn_inv{ proj.ldcf(root.poly) });
}

void cell_represents(datastructures::projections& proj, properties::properties& props, const Model& sample, const cell_at_level& representative) {
    if (representative.lower()) {
        root_represents(proj, props, sample, *representative.lower());
    }
    if (representative.upper()) {
        root_represents(proj, props, sample, *representative.upper());
    }
}

// TODO defer computation of resultants to next level


}