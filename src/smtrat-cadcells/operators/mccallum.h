#pragma once

#include "../datastructures/roots.h"

#include "mccallum_properties.h"
#include "mccallum_rules.h"


namespace smtrat::cadcells::operators::mccallum {

datastructures::cell_at_level construct_cell(datastructures::projections& projections, properties::properties& properties, const Model& sample) {
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

    auto main_var = projections.var_order()[properties.level()-1];
    delineation del(main_var);
    for(const auto& prop : properties.get<properties::poly_irreducible_sgn_inv>()) {
        delineate(projections, del, prop);
    }
    del.set_sample(sample[main_var]);

    // TODO construct cell from delineation



}

}
