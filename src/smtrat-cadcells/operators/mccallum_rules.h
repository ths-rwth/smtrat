#pragma once

#include "mccallum_properties.h"

namespace smtrat::cadcells::operators::mccallum::rules {

void root_well_def(projections& proj, properties& props, const Model& sample, poly_ref poly, size_t idx) {
    assert(props.contains(properties::poly_pdel(poly)));

    if (i != 1 && i != projections.num_roots(sample, poly)) return;
    else if (!projections.is_ldcf_zero(sample, poly)) return;
    else {
        props.insert(properties::poly_sgn_inv(projections.ldcf(poly)));
    }
}

void poly_pdel(projections& proj, properties& props, const Model& sample, poly_ref poly) {
    props.insert(properties::poly_non_null(poly));
    props.insert(properties::poly_ord_inv(projections.disc(poly)));
}


void poly_ord_inv(projections& proj, properties& props, const Model& sample, poly_ref poly) {
    auto factors = proj.factors_nonconst(poly);
    for (const auto& factor : factors) {
        poly_irrecubile_ord_inv(proj, props, sample, factor);
    }
}

void poly_irrecubile_ord_inv(projections& proj, properties& props, const Model& sample, poly_ref poly) {
    props.insert(properties::poly_irreducible_sgn_inv(poly));
    if (proj.is_zero(sample, poly)) {
        props.insert(properties::poly_pdel(poly));
    }
}


void poly_sgn_inv(projections& proj, properties& props, const Model& sample, poly_ref poly) {
    if (props.contains(properties::poly_ord_inv(poly))) return;
    else {
        auto factors = proj.factors_nonconst(poly);
        for (const auto& factor : factors) {
            props.insert(properties::poly_irreducible_sgn_inv(poly));
        }
    }
}

}