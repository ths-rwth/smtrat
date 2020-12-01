#pragma once

#include "mccallum_properties.h"
#include "mccallum_rules.h"

#include "projection.h"

namespace smtrat::cadcells::operators::mccallum {

cell_at_level construct_cell(projections& projections, properties& properties, const Model& sample) {
    for(const auto& prop : properties.get<properties::root_well_def>()) {
        rules::root_well_def(projections, properties, sample, prop.poly, prop.idx);
    }
    for(const auto& prop : properties.get<properties::poly_pdel>()) {
        rules::poly_pdel(projections, properties, sample, prop.poly);
    }
    for(const auto& prop : properties.get<properties::poly_non_null>()) {
        rules::poly_non_null(projections, properties, sample, prop.poly);
    }
    for(const auto& prop : properties.get<properties::poly_oi>()) {
        rules::poly_ord_inv(projections, properties, sample, prop.poly);
    }
    for(const auto& prop : properties.get<properties::poly_si>()) {
        rules::poly_sgn_inv(projections, properties, sample, prop.poly);
    }

    std::vector<poly_ref> nullified;
    std::vector<poly_ref> non_nullified;
    for(const auto& prop : properties.get<properties::poly_irreducible_si>()) {
        if (projections.nullified(sample, prop.poly)) {
            nullified.push_back(prop.poly);
        } else {
            non_nullified.push_back(prop.poly);
        }
    }

    // TODO


}
    
}
