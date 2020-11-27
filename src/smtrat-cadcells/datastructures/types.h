#pragma once

#include "../common.h"
#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/model.h>

namespace smtrat::cadcells::datastructures {

struct indexed_root {
    Poly poly;
    size_t index;
};
std::ostream& operator<<(std::ostream& os, const indexed_root& data) {
    os << "root(" << data.poly << ", " << data.index << ")";
    return os;
}

using var_order = std::vector<carl::Variable> m_variables;

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
size_t level_of(const var_order& order, const Poly& poly) {
    // assert(isSubset(asVector(poly.gatherVariables()), order));
    auto poly_variables = carl::variables(poly).underlyingVariableSet();
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

enum class bound { infty, weak };
struct cell_at_level {
private: 
    enum class type { section, sector /*, sector_lweak, sector_uweak, sector_weak*/ };

    std::optional<indexed_root> m_lower;
    std::optional<indexed_root> m_upper;
    type m_type;

public:

    cell_at_level(indexed_root bound) : m_lower(bound), m_type(type::section) {}
    cell_at_level(indexed_root lower, indexed_root upper) : m_lower(lower), m_upper(upper), m_type(type::sector) {}
    cell_at_level(bound lower, indexed_root upper) : m_upper(upper), m_type(type::sector) {}
    cell_at_level(indexed_root lower, bound upper) : m_lower(lower), m_type(type::sector) {}

    bool is_sector() const {
        return m_type == type::sector;
    }

    bool is_section() const {
        return m_type == type::section;
    }

    // TODO finish ...

};

}