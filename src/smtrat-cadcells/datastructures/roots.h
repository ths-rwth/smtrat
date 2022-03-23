#pragma once

#include "../common.h"
#include "polynomials.h"

namespace smtrat::cadcells::datastructures {

using carl::operator<<;

/**
 * Represents the i-th root of a multivariate polynomial at its main variable (given an appropriate sample).
 */
struct IndexedRoot {
    /// A multivariate polynomial.
    PolyRef poly;
    /// The index, must be > 0.
    size_t index;
    IndexedRoot(PolyRef p, size_t i) : poly(p), index(i) { assert(i>0); }
    IndexedRoot() : IndexedRoot( PolyRef{0,0}, 1) {}
};
inline bool operator==(const IndexedRoot& lhs, const IndexedRoot& rhs) {
    return lhs.poly == rhs.poly && lhs.index == rhs.index;
}
inline bool operator<(const IndexedRoot& lhs, const IndexedRoot& rhs) {
    return lhs.poly < rhs.poly || (lhs.poly == rhs.poly &&  lhs.index < rhs.index);
}
inline bool operator!=(const IndexedRoot& lhs, const IndexedRoot& rhs) {
    return !(lhs == rhs);
}
inline std::ostream& operator<<(std::ostream& os, const IndexedRoot& data) {
    os << "root(" << data.poly << ", " << data.index << ")";
    return os;
}

/// Bound type.
enum class Bound { infty };
/**
 * Holds the description of a cell.
 * A cell is either a section [xi,xi] or a section (-00,xi), (xi, xi'), (xi, oo) where xi,xi' are indexed roots.
 */
class CellDescription {
    enum class type { section, sector };

    std::optional<IndexedRoot> m_lower;
    std::optional<IndexedRoot> m_upper;
    type m_type;

public:

    CellDescription(IndexedRoot bound) : m_lower(bound), m_type(type::section) {}
    CellDescription(IndexedRoot lower, IndexedRoot upper) : m_lower(lower), m_upper(upper), m_type(type::sector) {}
    CellDescription(Bound, IndexedRoot upper) : m_upper(upper), m_type(type::sector) {}
    CellDescription(IndexedRoot lower, Bound) : m_lower(lower), m_type(type::sector) {}
    CellDescription(Bound, Bound) : m_type(type::sector) {}
    CellDescription() : m_type(type::sector) {}

    bool is_sector() const {
        return m_type == type::sector;
    }

    bool is_section() const {
        return m_type == type::section;
    }

    /**
     * In case of a section, the defining indexed root is returned.
     */
    const IndexedRoot& section_defining() const {
        assert(is_section());
        return *m_lower;
    }

    /**
     * Returns the lower bound as IndexedRoot if finite or std::nullopt if the lower bound is -oo.
     * 
     * Asserts that the cell is a sector.
     */
    const auto& lower() const {
        assert(is_sector());
        return m_lower;
    }

    /**
     * Returns the upper bound as IndexedRoot if finite or std::nullopt if the upper bound is oo.
     * 
     * Asserts that the cell is a sector.
     */
    const auto& upper() const {
        assert(is_sector());
        return m_upper;
    }

    std::optional<IndexedRoot> lower_defining() const {
        if (is_sector()) return lower();
        else return section_defining();
    }

    std::optional<IndexedRoot> upper_defining() const {
        if (is_sector()) return upper();
        else return section_defining();
    }

    boost::container::flat_set<PolyRef> polys() const {
        boost::container::flat_set<PolyRef> result;
        if (m_lower) result.insert(m_lower->poly);
        if (m_upper) result.insert(m_upper->poly);
        return result;
    }
};
inline std::ostream& operator<<(std::ostream& os, const CellDescription& data) {
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
 * Describes a covering of the real line by CellDescriptions (given an appropriate sample).
 */
class CoveringDescription {
    std::vector<CellDescription> m_data;

public:
    /**
     * Add a CellDescription to the covering.
     * 
     * The added cell needs to be the rightmost cell of the already added cells and not be contained in any of these cells (or vice versa).
     * 
     * * The first cell needs to have -oo as left bound.
     * * The last cell needs to have oo as right bound.
     * * All cells need to cover the real line under an appropriate sample.
     * * Evaluated under an appropriate sample, the left bound of the added cell c is strictly greater than the left bounds of already added cells (considering also "strictness" of the bounds).
     * * The right bound of the added cell c needs to be greater than all right bounds of already added cells (considering also "strictness" of the bounds).
     */
    void add(const CellDescription& c) {
        assert(!m_data.empty() || (c.is_sector() && !c.lower()));
        assert(m_data.empty() || c.is_section() || c.lower());
        assert(m_data.empty() || m_data.back().is_section() || m_data.back().upper());
        m_data.push_back(c);
    }

    const auto& cells() const {
        return m_data;
    }
};
inline std::ostream& operator<<(std::ostream& os, const CoveringDescription& data) {
    os << data.cells();
    return os;
}

/**
 * Describes an ordering of IndexedRoots with respect to a CellDescription (which is given implicitly).
 */
class IndexedRootOrdering {
    std::vector<std::pair<IndexedRoot, IndexedRoot>> m_data_below;
    std::vector<std::pair<IndexedRoot, IndexedRoot>> m_data_above;

    void add(std::vector<std::pair<IndexedRoot, IndexedRoot>>& data, IndexedRoot first, IndexedRoot second) {
        assert(first.poly.level == second.poly.level);
        assert(first != second);
        data.push_back(std::make_pair(first, second));
    }

public:
    /**
     * First is the root closer to the lower bound.
     * 
     * Relations need to be added in descending order of the first elements.
     */
    void add_below(IndexedRoot first, IndexedRoot second) {
        return add(m_data_below, first, second);
    }

    /**
     * First is the root closer to the upper bound.
     * 
     * Relations need to be added in ascending order of the first elements.
     */
    void add_above(IndexedRoot first, IndexedRoot second) {
        return add(m_data_above, first, second);
    }

    const auto& below() const {
        return m_data_below;
    }

    const auto& above() const {
        return m_data_above;
    }

    bool poly_has_lower(PolyRef poly) const {
        return std::find_if(below().begin(), below().end(), [&poly](const auto& rel) { return rel.second.poly == poly; }) != below().end();
    }

    bool poly_has_upper(PolyRef poly) const {
        return std::find_if(above().begin(), above().end(), [&poly](const auto& rel) { return rel.second.poly == poly; }) != above().end();
    }

    boost::container::flat_set<PolyRef> polys() const {
        boost::container::flat_set<PolyRef> result;
        for (const auto& pair : m_data_below) {
            result.insert(pair.first.poly);
            result.insert(pair.second.poly);
        }
        for (const auto& pair : m_data_above) {
            result.insert(pair.first.poly);
            result.insert(pair.second.poly);
        }
        return result;
    }
};
inline std::ostream& operator<<(std::ostream& os, const IndexedRootOrdering& data) {
    os << data.below() << " " << data.above();
    return os;
}

/**
 * Describes an ordering of IndexedRoots.
 */
class GeneralIndexedRootOrdering {
    std::vector<std::pair<IndexedRoot, IndexedRoot>> m_data;

public:
    /**
     * Relations need to be added in ascending order of the first elements.
     */
    void add(IndexedRoot first, IndexedRoot second) {
        assert(first.poly.level == second.poly.level);
        assert(first != second);
        m_data.push_back(std::make_pair(first, second));
    }

    const auto& data() const {
        return m_data;
    }
};
inline std::ostream& operator<<(std::ostream& os, const GeneralIndexedRootOrdering& data) {
    os << data.data();
    return os;
}

}