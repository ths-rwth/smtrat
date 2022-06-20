#pragma once

#include "properties.h"

/**
 * Functions for adding the delineation of a property.
 * 
 * The delineation of a property is a set of indexed root expressions representing the critical points of the property.
 * 
 * E.g. for sign invariance of a polynomial, it is the set of roots of the polynomial.
 * 
 */
namespace smtrat::cadcells::operators::delineation {

template<typename P>
void delineate(datastructures::DelineatedDerivation<P>& deriv, const properties::poly_irreducible_sgn_inv& prop) {
    if (deriv.proj().is_nullified(deriv.underlying_sample(), prop.poly)) {
        deriv.delin().add_poly_nullified(prop.poly);
    } else {
        auto roots = deriv.proj().real_roots(deriv.underlying_sample(), prop.poly);
        if (roots.empty()) {
            deriv.delin().add_poly_nonzero(prop.poly);
        } else {
            for (size_t idx = 0; idx < roots.size(); idx++) {
                deriv.delin().add_root(roots[idx], datastructures::IndexedRoot(prop.poly, idx+1));
            }
        }
    }
}
    
}