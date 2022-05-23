#pragma once

#include <map>
#include <vector>
#include <boost/container/flat_set.hpp>

#include "roots.h"

namespace smtrat::cadcells::datastructures {

using RootMap = std::map<RAN, std::vector<IndexedRoot>>;

/**
 * An interval of a delineation.
 */
class DelineationInterval {
    RootMap::const_iterator m_lower;
    RootMap::const_iterator m_upper;
    RootMap::const_iterator m_end;

    bool is_inclusive_l;
    bool is_inclusive_u;

    DelineationInterval(RootMap::const_iterator&& lower, RootMap::const_iterator&& upper, RootMap::const_iterator&& end) : m_lower(lower), m_upper(upper), m_end(end) {
        // Default: Only sections have closed bounds
        is_inclusive_l = is_section();
        is_inclusive_u = is_section();
    };

    friend class Delineation;

public:
    bool is_section() const {
        return m_lower != m_end && m_upper != m_end && m_lower == m_upper;
    }

    bool is_sector() const {
        return !is_section();
    }

    const auto& lower() const {
        assert(m_lower != m_end);
        return m_lower;
    }
    bool lower_unbounded() const {
        return m_lower == m_end;
    }

    const auto& upper() const {
        assert(m_upper != m_end);
        return m_upper;
    }
    bool upper_unbounded() const {
        return m_upper == m_end;
    }

    bool lower_inclusive() const {
        return is_inclusive_l;
    }
    bool upper_inclusive() const {
        return is_inclusive_u;
    }

    void set_lower_inclusive() {
        if(is_sector()) {
            is_inclusive_l = true;
        }
    }
    void set_upper_inclusive() {
        if(is_sector()) {
            is_inclusive_u = true;
        }
    }
};    
inline std::ostream& operator<<(std::ostream& os, const DelineationInterval& data) {
    if (data.is_section()) { // Redundant, but for readability
        os << "[" << *data.lower() << ", " << *data.upper() << "]";
    } else if (!data.lower_unbounded() && !data.upper_unbounded() && data.lower_inclusive() && data.upper_inclusive()) {
        os << "[" << *data.lower() << ", " << *data.upper() << "]";
    } else if (!data.lower_unbounded() && !data.upper_unbounded() && data.lower_inclusive() && !data.upper_inclusive()) {
        os << "[" << *data.lower() << ", " << *data.upper() << ")";
    } else if (!data.lower_unbounded() && !data.upper_unbounded() && !data.lower_inclusive() && data.upper_inclusive()) {
        os << "(" << *data.lower() << ", " << *data.upper() << "]";
    } else if (!data.lower_unbounded() && !data.upper_unbounded() && !data.lower_inclusive() && !data.upper_inclusive()) {
        os << "(" << *data.lower() << ", " << *data.upper() << ")";
    } else if (!data.lower_unbounded() && !data.lower_inclusive()) {
        os << "(" << *data.lower() << ", oo)";
    } else if (!data.lower_unbounded() && data.lower_inclusive()) {
        os << "[" << *data.lower() << ", oo)";
    } else if (!data.upper_unbounded() && !data.upper_inclusive()) {
        os << "(-oo, " << *data.upper() << ")";
    } else if (!data.upper_unbounded() && data.upper_inclusive()) {
        os << "(-oo, " << *data.upper() << "]";
    } else {
        os << "(-oo, oo)";
    }
    return os;

}

/**
 * Represents the delineation of a set of polynomials (at a sample), that is
 * - the ordering of all roots,
 * - the set of nullified polynomials,
 * - the set of polynomials without a root.
 */
class Delineation {
    friend class DelineationInterval;

    /// A map from the actual roots to indexed root expressions. Note that this map is sorted.
    RootMap m_roots;
    /// The set of all nullified polynomials.
    boost::container::flat_set<PolyRef> m_polys_nullified;
    /// The set of all polynomials without a root.
    boost::container::flat_set<PolyRef> m_polys_noroot;

public: 
    Delineation() {}

    /**
     * Returns the underlying root map, which is a set of real algebraic numbers to indexed root expressions.
     */
    const auto& roots() const {
        return m_roots;
    }
    /**
     * The set of nullified polynomials.
     */
    const auto& nullified() const {
        return m_polys_nullified;
    }
    /**
     * The set of polynomials without roots.
     */
    const auto& nonzero() const {
        return m_polys_noroot;
    }
    bool empty() const {
        return m_roots.empty() && m_polys_nullified.empty() && m_polys_noroot.empty();
    }

    /**
     * Computes the bounds of the interval around the given sample w.r.t. this delineation. 
     */
    auto delineate_cell(const RAN& sample) const {
        RootMap::const_iterator lower;
        RootMap::const_iterator upper;

        if (m_roots.empty()) {
            lower = m_roots.end();
            upper = m_roots.end();
        } else {
            auto section = m_roots.find(sample);
            if (section != m_roots.end()) {
                lower = section;
                upper = section;
            } else {
                upper = m_roots.upper_bound(sample);
                if (upper == m_roots.begin()) {
                    lower = m_roots.end();
                } else {
                    lower = upper;
                    lower--;
                }
            }
        }
        
        return DelineationInterval(std::move(lower),std::move(upper),m_roots.end());
    }

    void add_root(RAN root, IndexedRoot ir_root) {
        auto irs = m_roots.find(root);
        if (irs == m_roots.end()) {
            irs = m_roots.emplace(std::move(root), std::vector<IndexedRoot>()).first;
        }
        auto loc = std::find(irs->second.begin(), irs->second.end(), ir_root);
        if (loc == irs->second.end()) {
            irs->second.push_back(std::move(ir_root));
        }
    }

    void add_poly_noroot(PolyRef poly) {
        m_polys_noroot.insert(poly);
    }

    void add_poly_nullified(PolyRef poly) {
        m_polys_nullified.insert(poly);
    }
};
inline std::ostream& operator<<(std::ostream& os, const Delineation& data) {
    os << "(roots: " << data.roots() << "; nonzero: " << data.nonzero() << "; nullified: "  << data.nullified() << ")";
    return os;
}

/**
 * Compares the lower bounds of two DelineationIntervals. It respects whether the interval is a section or sector.
 */
inline bool lower_lt_lower(const DelineationInterval& del1, const DelineationInterval& del2) {
    if (del1.lower_unbounded()) return !del2.lower_unbounded();
    else if (del2.lower_unbounded()) return false;
    else if (del1.lower()->first == del2.lower()->first) return del1.lower_inclusive() && !del2.lower_inclusive(); // Now a sector is no guarantee for containing a lower value
    else return del1.lower()->first < del2.lower()->first;
}

/**
 * Compares the lower bounds of two DelineationIntervals. It respects whether the interval is a section or sector.
 */
inline bool lower_eq_lower(const DelineationInterval& del1, const DelineationInterval& del2) {
    if (del1.lower_unbounded() && del2.lower_unbounded()) return true;
    else if (del1.lower_unbounded() != del2.lower_unbounded()) return false;
    else if (del1.lower()->first == del2.lower()->first) return del1.lower_inclusive() == del2.lower_inclusive();
    else return false;
}

/**
 * Compares the upper bounds of two DelineationIntervals. It respects whether the interval is a section or sector.
 */
inline bool upper_lt_upper(const DelineationInterval& del1, const DelineationInterval& del2) {
    if (del1.upper_unbounded()) return false;
    else if (del2.upper_unbounded()) return true;
    else if (del1.upper()->first == del2.upper()->first) return !del1.upper_inclusive() && del2.upper_inclusive(); // Now a sector is no guarantee for containing a lower value
    else return del1.upper()->first < del2.upper()->first;
}

/**
 * Compares an upper bound with a lower bound of DelineationIntervals. It respects whether the interval is a section or sector.
 */
inline bool upper_lt_lower(const DelineationInterval& del1, const DelineationInterval& del2) {
    if (del1.upper_unbounded()) return false;
    if (del2.lower_unbounded()) return false;
    if (del1.upper()->first < del2.lower()->first) return true;
    if (del1.upper()->first == del2.lower()->first && (!del1.upper_inclusive() && !del2.lower_inclusive())) return true;
    return false;
}


} 