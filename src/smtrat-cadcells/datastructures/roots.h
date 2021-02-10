#pragma once

#include "../common.h"
#include "polynomials.h"

namespace smtrat::cadcells::datastructures {

using carl::operator<<;

/**
 * Represents the i-th root of a multivariate polynomial at its main variable (given an appropriate sample).
 */
struct indexed_root {
    /// A multivariate polynomial.
    poly_ref poly;
    /// The index, must be > 0.
    size_t index;
    indexed_root(poly_ref p, size_t i) : poly(p), index(i) { assert(i>0); }
    indexed_root() : indexed_root( poly_ref{0,0}, 1) {}
};
bool operator==(const indexed_root& lhs, const indexed_root& rhs) {
    return lhs.poly == rhs.poly && lhs.index == rhs.index;
}
bool operator<(const indexed_root& lhs, const indexed_root& rhs) {
    return lhs.poly < rhs.poly || (lhs.poly == rhs.poly &&  lhs.index < rhs.index);
}
bool operator!=(const indexed_root& lhs, const indexed_root& rhs) {
    return !(lhs == rhs);
}
std::ostream& operator<<(std::ostream& os, const indexed_root& data) {
    os << "root(" << data.poly << ", " << data.index << ")";
    return os;
}

/// Bound type.
enum class bound { infty };
/**
 * Holds the description of a cell.
 * A cell is either a section [xi,xi] or a section (-00,xi), (xi, xi'), (xi, oo) where xi,xi' are indexed roots.
 */
class cell_description {
    enum class type { section, sector };

    std::optional<indexed_root> m_lower;
    std::optional<indexed_root> m_upper;
    type m_type;

public:

    cell_description(indexed_root bound) : m_lower(bound), m_type(type::section) {}
    cell_description(indexed_root lower, indexed_root upper) : m_lower(lower), m_upper(upper), m_type(type::sector) {}
    cell_description(bound, indexed_root upper) : m_upper(upper), m_type(type::sector) {}
    cell_description(indexed_root lower, bound) : m_lower(lower), m_type(type::sector) {}
    cell_description(bound, bound) : m_type(type::sector) {}
    cell_description() : m_type(type::sector) {}

    bool is_sector() const {
        return m_type == type::sector;
    }

    bool is_section() const {
        return m_type == type::section;
    }

    /**
     * In case of a section, the defining indexed root is returned.
     */
    const indexed_root& section_defining() const {
        assert(is_section());
        return *m_lower;
    }

    /**
     * Returns the lower bound as indexed_root if finite or std::nullopt if the lower bound is -oo.
     * 
     * Asserts that the cell is a sector.
     */
    const auto& lower() const {
        assert(is_sector());
        return m_lower;
    }

    /**
     * Returns the upper bound as indexed_root if finite or std::nullopt if the upper bound is oo.
     * 
     * Asserts that the cell is a sector.
     */
    const auto& upper() const {
        assert(is_sector());
        return m_upper;
    }

    std::optional<indexed_root> lower_defining() const {
        if (is_sector()) return lower();
        else return section_defining();
    }

    std::optional<indexed_root> upper_defining() const {
        if (is_sector()) return upper();
        else return section_defining();
    }
};
std::ostream& operator<<(std::ostream& os, const cell_description& data) {
    if (data.is_section()) {
        os << "[" << data.section_defining() << ", " << data.section_defining() << "]";
    } else if (data.lower() && data.upper()) {
        os << "(" << *data.lower() << ", " << *data.upper() << ")";
    } else if (data.lower()) {
        os << "(" << *data.lower() << ", oo)";
    } else if (data.upper()) {
        os << "(-oo, " << *data.upper() << ")";
    } else {
        os << "(-oo, oo)";
    }
    return os;
}

/**
 * Describes a covering of the real line by cell_descriptions (given an appropriate sample).
 */
class covering_description {
    std::vector<cell_description> m_data;

public:
    /**
     * Add a cell_description to the covering.
     * 
     * The added cell needs to be the rightmost cell of the already added cells and not be contained in any of these cells (or vice versa).
     * 
     * * The first cell needs to have -oo as left bound.
     * * The last cell needs to have oo as right bound.
     * * All cells need to cover the real line under an appropriate sample.
     * * Evaluated under an appropriate sample, the left bound of the added cell c is strictly greater than the left bounds of already added cells (considering also "strictness" of the bounds).
     * * The right bound of the added cell c needs to be greater than all right bounds of already added cells (considering also "strictness" of the bounds).
     */
    void add(const cell_description& c) {
        assert(!m_data.empty() || (c.is_sector() && !c.lower()));
        assert(m_data.empty() || c.is_section() || c.lower());
        assert(m_data.empty() || m_data.back().is_section() || m_data.back().upper());
        m_data.push_back(c);
    }

    const auto& cells() const {
        return m_data;
    }
};
std::ostream& operator<<(std::ostream& os, const covering_description& data) {
    os << data.cells();
    return os;
}

/**
 * Describes an ordering of indexed_roots with respect to a cell_description (which is given implicitly).
 */
class indexed_root_ordering {
    std::vector<std::pair<indexed_root, indexed_root>> m_data_below;
    std::vector<std::pair<indexed_root, indexed_root>> m_data_above;

    void add(std::vector<std::pair<indexed_root, indexed_root>>& data, indexed_root first, indexed_root second) {
        assert(first.poly.level == second.poly.level);
        assert(first != second);
        data.push_back(std::make_pair(first, second));
    }

public:
    /**
     * Second is the root closer to the lower bound.
     * 
     * Relations need to be added in descending order of the second elements.
     */
    void add_below(indexed_root first, indexed_root second) {
        return add(m_data_below, first, second);
    }

    /**
     * First is the root closer to the upper bound.
     * 
     * Relations need to be added in ascending order of the first elements.
     */
    void add_above(indexed_root first, indexed_root second) {
        return add(m_data_above, first, second);
    }

    const auto& below() const {
        return m_data_below;
    }

    const auto& above() const {
        return m_data_above;
    }
};
std::ostream& operator<<(std::ostream& os, const indexed_root_ordering& data) {
    os << data.below() << " " << data.above();
    return os;
}

}