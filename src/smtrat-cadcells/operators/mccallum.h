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

    std::vector<datastructures::poly_ref> nullified;
    std::vector<datastructures::poly_ref> non_nullified;
    for(const auto& prop : properties.get<properties::poly_irreducible_sgn_inv>()) {
        if (projections.is_nullified(sample, prop.poly)) {
            nullified.push_back(prop.poly);
        } else {
            non_nullified.push_back(prop.poly);
        }
    }

    // TODO


}

}
