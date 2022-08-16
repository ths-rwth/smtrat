#pragma once

#include <map>
#include <vector>
#include <boost/container/flat_set.hpp>

#include "roots.h"

namespace smtrat::cadcells::datastructures {

struct TaggedIndexedRoot {
    IndexedRoot root;
    bool is_inclusive;
    bool is_optional;
};
inline std::ostream& operator<<(std::ostream& os, const TaggedIndexedRoot& data) {
    os << data.root;
    if (data.is_inclusive) os << "_incl";
    if (data.is_optional) os << "_opt";
    return os;
}
bool operator==(const TaggedIndexedRoot& lhs, const TaggedIndexedRoot& rhs) {
    return lhs.root == rhs.root && lhs.is_inclusive == rhs.is_inclusive && lhs.is_optional == rhs.is_optional;
}
bool operator<(const TaggedIndexedRoot& lhs, const TaggedIndexedRoot& rhs) {
    return lhs.root < rhs.root || (lhs.root == rhs.root && lhs.is_inclusive < rhs.is_inclusive) || (lhs.root == rhs.root && lhs.is_inclusive == rhs.is_inclusive && lhs.is_optional < rhs.is_optional);
}

using RootMap = std::map<RAN, std::vector<TaggedIndexedRoot>>;

/**
 * An interval of a delineation.
 */
class DelineationInterval {
    RootMap::const_iterator m_lower;
    RootMap::const_iterator m_upper;
    RootMap::const_iterator m_end;
    bool m_lower_strict;
    bool m_upper_strict;

    DelineationInterval(RootMap::const_iterator&& lower, RootMap::const_iterator&& upper, RootMap::const_iterator&& end, bool lower_strict, bool upper_strict) : m_lower(lower), m_upper(upper), m_end(end), m_lower_strict(lower_strict), m_upper_strict(upper_strict) {
        assert(!is_section() || (!lower_strict && !upper_strict));
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
    bool lower_strict() const {
        return !lower_unbounded() && m_lower_strict;
    }

    const auto& upper() const {
        assert(m_upper != m_end);
        return m_upper;
    }
    bool upper_unbounded() const {
        return m_upper == m_end;
    }
    bool upper_strict() const {
        return !upper_unbounded() && m_upper_strict;
    }

    bool contains(const RAN& sample) const {
        if (is_section()) {
            return sample == lower()->first;
        } else {
            if (!lower_unbounded() && lower_strict() && sample <= lower()->first) return false;
            if (!lower_unbounded() && !lower_strict() && sample < lower()->first) return false;
            if (!upper_unbounded() && upper_strict() && sample >= upper()->first) return false;
            if (!upper_unbounded() && !upper_strict() && sample >= upper()->first) return false;
            return true;
        }
    }
};    
inline std::ostream& operator<<(std::ostream& os, const DelineationInterval& data) {
    if (data.lower_strict()) {
        os << "(" << *data.lower();
    } else if (data.lower_unbounded()) {
        os << "(-oo";
    } else {
        os << "[" << *data.lower();
    }
    os << ", ";
    if (data.upper_strict()) {
        os << *data.upper() << ")";
    } else if (data.upper_unbounded()) {
        os << "oo)";
    } else {
        os << *data.upper() << "]";
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
    boost::container::flat_set<PolyRef> m_polys_nonzero;

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
        return m_polys_nonzero;
    }
    bool empty() const {
        return m_roots.empty() && m_polys_nullified.empty() && m_polys_nonzero.empty();
    }

    /**
     * Computes the bounds of the interval around the given sample w.r.t. this delineation. 
     */
    auto delineate_cell(const RAN& sample) const {
        RootMap::const_iterator lower;
        RootMap::const_iterator upper;
        bool lower_strict = false;
        bool upper_strict = false;

        if (m_roots.empty()) {
            lower = m_roots.end();
            upper = m_roots.end();
        } else {
            lower = m_roots.lower_bound(sample);
            if (lower == m_roots.end() || lower->first != sample) {
                if (lower == m_roots.begin()) lower = m_roots.end();
                else lower--;
            }
            while(lower != m_roots.end() && std::find_if(lower->second.begin(), lower->second.end(), [&](const auto& t_root) { return !t_root.is_optional; }) == lower->second.end()) {
                if (lower == m_roots.begin()) lower = m_roots.end();
                else lower--;
            }
            upper = m_roots.lower_bound(sample);
            while(upper != m_roots.end() && std::find_if(upper->second.begin(), upper->second.end(), [&](const auto& t_root) { return !t_root.is_optional; }) == upper->second.end()) {
                upper++;
            }
            /*
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
            */
        }

        if (lower != upper) {
            if(lower != m_roots.end()) {
                lower_strict = std::find_if(lower->second.begin(), lower->second.end(), [&](const auto& t_root) { return !t_root.is_inclusive; }) != lower->second.end();
            }
            if(upper != m_roots.end()) {
                upper_strict = std::find_if(upper->second.begin(), upper->second.end(), [&](const auto& t_root) { return !t_root.is_inclusive; }) != upper->second.end();
            }
        }

        return DelineationInterval(std::move(lower), std::move(upper), m_roots.end(), lower_strict, upper_strict);
    }

    void add_root(RAN root, IndexedRoot ir_root, bool inclusive, bool optional = false) {
        auto irs = m_roots.find(root);
        if (irs == m_roots.end()) {
            irs = m_roots.emplace(std::move(root), std::vector<TaggedIndexedRoot>()).first;
        }
        auto tagged_root = TaggedIndexedRoot {ir_root, inclusive, optional};
        auto loc = std::find(irs->second.begin(), irs->second.end(), tagged_root);
        if (loc == irs->second.end()) {
            irs->second.push_back(std::move(tagged_root));
        }
    }

    void add_poly_nonzero(PolyRef poly) {
        m_polys_nonzero.insert(poly);
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
    else if (del1.lower()->first == del2.lower()->first) return !del1.lower_strict() && del2.lower_strict();
    else return del1.lower()->first < del2.lower()->first;
}

/**
 * Compares the lower bounds of two DelineationIntervals. It respects whether the interval is a section or sector.
 */
inline bool lower_eq_lower(const DelineationInterval& del1, const DelineationInterval& del2) {
    if (del1.lower_unbounded() && del2.lower_unbounded()) return true;
    else if (del1.lower_unbounded() != del2.lower_unbounded()) return false;
    else if (del1.lower()->first == del2.lower()->first) return del1.lower_strict() == del2.lower_strict();
    else return false;
}

/**
 * Compares the upper bounds of two DelineationIntervals. It respects whether the interval is a section or sector.
 */
inline bool upper_lt_upper(const DelineationInterval& del1, const DelineationInterval& del2) {
    if (del1.upper_unbounded()) return false;
    else if (del2.upper_unbounded()) return true;
    else if (del1.upper()->first == del2.upper()->first) return del1.upper_strict() && !del2.upper_strict();
    else return del1.upper()->first < del2.upper()->first;
}

/**
 * Compares an upper bound with a lower bound of DelineationIntervals. It respects whether the interval is a section or sector.
 */
inline bool upper_lt_lower(const DelineationInterval& del1, const DelineationInterval& del2) {
    if (del1.upper_unbounded()) return false;
    if (del2.lower_unbounded()) return false;
    if (del1.upper()->first < del2.lower()->first) return true;
    if (del1.upper()->first == del2.lower()->first && del1.upper_strict() && del2.upper_strict()) return true;
    return false;
}


} 