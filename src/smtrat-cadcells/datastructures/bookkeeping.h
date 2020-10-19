#pragma once

#include "../common.h"
#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/model.h>

namespace smtrat::cadcells::datastructures {

using var_order = std::vector<carl::Variable> m_variables;

/**
 * Find the index of the highest variable (wrt. the ordering in 'order') that occurs with positive degree in 'poly'.
 * We start counting at 1 and represent "no level/variable" as 0 because it simplifies using the level directly as an index into arrays or vectors.
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
size_t level_of(const var_order& order, const Poly& poly) {
    // assert(isSubset(asVector(poly.gatherVariables()), order));
    auto poly_variables = carl::variables(poly).underlyingVariableSet();
    if (poly_variables.empty()) {
        // polynomial is constant
        return 0;
    }
    for (std::size_t level = 0; level < order.size(); ++level) {
        polyVariables.erase(order[level]);
        if (polyVariables.empty()) return level;
    }
    assert(false && "Poly contains variable not found in order"); // precondition violated
    return 0;
}

class properties {
    size_t m_level;
    const var_order& m_var_order;
    properties& m_lower; 
    std::set<property> m_properties_at_level;

private:
    void insert_at_level(size_t level, property&& property) {
        assert(level <= m_level);
        if (level < m_level) {
            assert(level > 0);
            m_lower.insert_at_level(level, std::move(property));
        } else {
            // TODO maybe support redundancy checks
            m_properties_at_level.emplace(std::move(property));
        }
    }

public:
    properties(const var_order& order) : m_var_order(order) {}

    void insert(property&& property) {
        insert_at_level(property.compute_level(m_var_order), std::move(property));
    }


};

}