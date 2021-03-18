#pragma once

#include "common.h"

namespace smtrat::cadcells::helper {

/**
 * Find the index of the highest variable (wrt. the ordering in 'order') that occurs with positive degree in 'poly'.
 * We start counting at 1 and represent "no level/variable" as 0.
 * Examples:
 * - level(2) == 0 wrt. any variable order
 * - level(0*x+2) == 0 wrt. any variable order
 * - level(x+2) == 1 wrt. [x < y < z]
 * - level(x+2) == 2 wrt. [y < x < z]
 * - level(x+2) == 3 wrt. [y < z < x]
 * - level(x*y+2) == 2 wrt. [x < y < z] because of y
 * - level(x*y+2) == 2 wrt. [y < x < z] because of x
 * - level(x*y+2) == 3 wrt. [x < z < y] because of y
 * Preconditions:
 * - 'poly.gatherVariables()' must be a subset of 'order'.
 */
size_t level_of(const VariableOrdering& order, const Poly& poly) {
    // assert(isSubset(asVector(poly.gatherVariables()), order));
    auto poly_variables = carl::variables(poly).as_set();
    if (poly_variables.empty()) {
        // polynomial is constant
        return 0;
    }
    for (std::size_t level = 1; level <= order.size(); ++level) {
        poly_variables.erase(order[level-1]);
        if (poly_variables.empty()) return level;
    }
    assert(false && "Poly contains variable not found in order"); // precondition violated
    return 0;
}

carl::Variable main_var(const VariableOrdering& order, const Poly& poly) {
    // assert(isSubset(asVector(poly.gatherVariables()), order));
    auto poly_variables = carl::variables(poly).as_set();
    if (poly_variables.empty()) {
        // polynomial is constant
        return carl::Variable::NO_VARIABLE;
    }
    for (std::size_t level = 0; level < order.size(); ++level) {
        if (poly_variables.size() == 1) return *poly_variables.begin();
        poly_variables.erase(order[level]);
    }
    assert(false && "Poly contains variable not found in order"); // precondition violated
    return carl::Variable::NO_VARIABLE;
}

}