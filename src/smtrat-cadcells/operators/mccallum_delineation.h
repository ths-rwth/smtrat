#pragma once

#include "mccallum_properties.h"

namespace smtrat::cadcells::operators::mccallum {

void delineate(datastructures::projections& proj, delineation& delineation, const assignment& sample, const properties::poly_irreducible_sgn_inv& prop) {
    if (proj.is_nullified(prop.poly)) {
        delineation.add_poly_nullified(prop.poly);
    } else {
        auto roots = proj.real_roots(sample, prop.poly);
        if (roots.empty()) {
            delineation.add_poly_noroot(prop.poly);
        } else {
            for (size_t idx = 0; idx < roots.size(); idx++) {
                delineation.add_root(roots[idx], indexed_root(prop.poly, idx));
            }
        }
    }
}
    
}