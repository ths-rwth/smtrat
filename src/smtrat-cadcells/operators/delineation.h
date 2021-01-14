#pragma once

#include "properties.h"

namespace smtrat::cadcells::operators::delineation {

void delineate(base_derivation& deriv, const properties::poly_irreducible_sgn_inv& prop) {
    if (deriv.proj().is_nullified(prop.poly)) {
        deriv.delineation().add_poly_nullified(prop.poly);
    } else {
        auto roots = deriv.proj().real_roots(deriv.underlying_sample(), prop.poly);
        if (roots.empty()) {
            deriv.delineation().add_poly_noroot(prop.poly);
        } else {
            for (size_t idx = 0; idx < roots.size(); idx++) {
                deriv.delineation().add_root(roots[idx], indexed_root(prop.poly, idx));
            }
        }
    }
}
    
}