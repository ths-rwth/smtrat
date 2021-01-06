#pragma once

#include "../datastructures/roots.h"

#include "mccallum_properties.h"
#include "mccallum_rules.h"


namespace smtrat::cadcells::operators::mccallum {

void project_basic_properties(datastructures::projections& projections, properties::properties& properties, const assignment& sample) {
    for(const auto& prop : properties.get<properties::root_well_def>()) {
        rules::root_well_def(projections, properties, sample, prop.poly, prop.idx);
    }
    for(const auto& prop : properties.get<properties::poly_ord_inv>()) {
        rules::poly_ord_inv(projections, properties, sample, prop.poly);
    }
    for(const auto& prop : properties.get<properties::poly_pdel>()) {
        rules::poly_pdel(projections, properties, sample, prop.poly);
    }
    for(const auto& prop : properties.get<properties::poly_sgn_inv>()) {
        rules::poly_sgn_inv(projections, properties, sample, prop.poly);
    }
}

auto delineate_cell_properties(datastructures::projections& projections, properties::properties& properties, const assignment& sample) {
    auto main_var = projections.var_order()[properties.level()-1];
    delineation del(main_var);
    for(const auto& prop : properties.get<properties::poly_irreducible_sgn_inv>()) {
        delineate(projections, del, sample, prop);
    }
    del.set_sample(sample[main_var]);
    return del;
}

void project_cell_properties(datastructures::projections& projections, properties::properties& properties, const assignment& sample, const delineation& del, const cell_representation& repr) {
    for(const auto& prop : properties.get<properties::poly_irreducible_sgn_inv>()) {
        if (repr->equational.find(prop.poly) == repr->equational.end()) {
            properties.insert(properties::poly_pdel{ poly });
        }
    }

    for (const auto& poly : del.nonzero()) {
        if (repr->equational.find(poly) == repr->equational.end()) {
            rules::poly_irrecubile_nonzero_sgn_inv(projections, properties, sample, poly);
        }
    }

    rules::cell_connected(projections, properties, sample, repr->cell);
    rules::cell_analytic_submanifold(projections, properties, sample, repr->cell);
    rules::cell_represents(projections, properties, sample, repr->cell);

    for (const auto& poly : repr.equational) {
        rules::poly_irrecubile_sgn_inv_ec(projections, properties, sample, repr->cell, poly);
    }

    rules::root_ordering_holds(projections, properties, sample, repr->cell, repr->ordering);

    for(const auto& prop : properties.get<properties::poly_irreducible_sgn_inv>()) {
        if (repr.equational.find(prop.poly) == repr.equational.end() && del.nonzero().find(prop.poly) == del.nonzero().end()) {
            rules::poly_irrecubile_sgn_inv(projections, properties, sample, repr->cell, repr->.ordering, prop.poly);
        }
    }
}

}
