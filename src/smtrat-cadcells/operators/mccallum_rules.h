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

void cell_connected(datastructures::projections& proj, properties::properties& props, const Model& sample, const cell& representative) {
    if (representative.is_sector() && representative.lower() && representative.upper() && representative.lower()->poly != representative.upper()->poly) {
        assert(props.contains(properties::poly_pdel{ representative.lower()->poly }));
        assert(props.contains(properties::poly_pdel{ representative.upper()->poly }));
        props.insert(properties::poly_ord_inv{ proj.res(representative.lower()->poly, representative.upper()->poly) });
    }
}

void cell_analytic_submanifold(datastructures::projections& proj, properties::properties& props, const Model& sample, const cell& representative) {
}

void poly_irrecubile_sgn_inv_ec(datastructures::projections& proj, properties::properties& props, const Model& sample, const cell& representative, datastructures::poly_ref poly) {
    assert(representative.is_section());
    assert(props.contains(properties::poly_pdel{ representative.sector_defining().poly }));
    assert(props.contains(properties::poly_sgn_inv{ proj.ldcf(representative.sector_defining().poly) }));
    if (representative.sector_defining().poly != poly) {
        props.insert(properties::poly_ord_inv{ proj.res(representative.sector_defining().poly, poly) });
    }
}

void root_represents(datastructures::projections& proj, properties::properties& props, const Model& sample, indexed_root root) {
    assert(props.contains(properties::poly_pdel{ root.poly }));
    props.insert(properties::poly_sgn_inv{ proj.ldcf(root.poly) });
}

void cell_represents(datastructures::projections& proj, properties::properties& props, const Model& sample, const cell& representative) {
    if (representative.lower()) {
        root_represents(proj, props, sample, *representative.lower());
    }
    if (representative.upper()) {
        root_represents(proj, props, sample, *representative.upper());
    }
}

void root_ordering_holds(datastructures::projections& proj, properties::properties& props, const Model& sample, const cell& representative, const indexed_root_ordering& ordering) {
    for (const auto& rel : ordering.data_below()) {
        if (rel.first.poly != rel.second.poly) {
            assert(props.contains(properties::poly_pdel{ rel.first.poly }));
            assert(props.contains(properties::poly_pdel{ rel.second.poly }));
            props.insert(properties::poly_ord_inv{ proj.res(rel.first.poly, rel.second.poly) });
            props.insert(properties::root_well_def{ rel.first });
        }
    }
    for (const auto& rel : ordering.data_above()) {
        if (rel.first.poly != rel.second.poly) {
            assert(props.contains(properties::poly_pdel{ rel.first.poly }));
            assert(props.contains(properties::poly_pdel{ rel.second.poly }));
            props.insert(properties::poly_ord_inv{ proj.res(rel.first.poly, rel.second.poly) });
            props.insert(properties::root_well_def{ rel.first });
        }
    }
}

void poly_irrecubile_sgn_inv(datastructures::projections& proj, properties::properties& props, const Model& sample, const cell& representative, const indexed_root_ordering& ordering, datastructures::poly_ref poly) {
    assert(props.contains(properties::poly_pdel{ poly }));
    if (representative.is_section() && proj.is_zero(sample, poly)) {
        auto roots = proj.real_roots(poly);
        auto it = std::find(roots.begin(), roots.end(), 0);
        props.insert(properties::root_well_def{ poly, std::distance(roots.begin(), it) + 1 });
    } else {
        assert(!proj.is_zero(sample, poly));
        if (representative.is_sector() && (del.lower_unbounded() || del.upper_unbounded())) {
            props.insert(properties::poly_sgn_inv{ proj.ldcf(poly) });
        } else {
            bool has_lower = (poly == representative.lower().poly) || std::find_if(ordering.below().begin(), ordering.below().end(), [&poly](const auto& rel) { return rel.second.poly == poly }) != ordering.below().end();
            bool has_upper = (poly == representative.upper().poly) || std::find_if(ordering.above().begin(), ordering.above().end(), [&poly](const auto& rel) { return rel.second.poly == poly }) != ordering.above().end();
            if (!(has_lower && has_upper)) {
                // TODO implement further checks
                props.insert(properties::poly_sgn_inv{ proj.ldcf(poly) });
            }
        }
    }
}

// TODO defer computation of resultants to next level

}