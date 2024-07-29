#pragma once

#include "../common.h"
#include "polynomials.h"
#include "boost/container/flat_set.hpp"
#include "boost/container/flat_map.hpp"

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
    IndexedRoot(PolyRef p, size_t i) : poly(p), index(i) { /*assert(i>0);*/ }
    IndexedRoot() : IndexedRoot( PolyRef{0,0,0}, 0) {}
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

struct IndexedRootConstraint {
    carl::Relation relation;
    IndexedRoot bound;
};
inline bool operator==(const IndexedRootConstraint& lhs, const IndexedRootConstraint& rhs) {
    return lhs.relation == rhs.relation && lhs.bound == rhs.bound;
}
inline bool operator<(const IndexedRootConstraint& lhs, const IndexedRootConstraint& rhs) {
    return lhs.relation < rhs.relation || (lhs.relation == rhs.relation &&  lhs.bound < rhs.bound);
}
inline bool operator!=(const IndexedRootConstraint& lhs, const IndexedRootConstraint& rhs) {
    return !(lhs == rhs);
}
inline std::ostream& operator<<(std::ostream& os, const IndexedRootConstraint& data) {
    os << "(var " << data.relation << " " << data.bound << ")";
    return os;
}

struct PiecewiseLinearInfo {
    /// Active linear bound from -oo to including the first intersection point (or oo if no such point exists)
    IndexedRoot first;
    /// List of intersection points and linear bounds which are active beginning from including the given intersection point to including the next intersection point (or oo if no such point exists); at intersection points, two bounds are active; the list needs to be sorted by intersection point
    std::vector<std::pair<Rational,IndexedRoot>> bounds;

    bool poly_bound_at(const PolyRef& poly, const RAN& r) const {
        if (bounds.empty()) return first.poly == poly;
        auto it = bounds.begin();
        while(it+1 != bounds.end() && r < (it+1)->first) it++;
        return it->second.poly == poly;
    }
};

/**
 * Represents the minimum function  of the contained indexed root functions.
 */
struct CompoundMinMax {
    std::vector<std::vector<IndexedRoot>> roots;
    void polys(boost::container::flat_set<PolyRef>& result) const {
        for (const auto& r : roots) {
            for (const auto& r1 : r) {
                result.insert(r1.poly);
            }
        }
    }
    std::optional<PiecewiseLinearInfo> bounds;
};
inline bool operator==(const CompoundMinMax& lhs, const CompoundMinMax& rhs) {
    return lhs.roots == rhs.roots;
}
inline bool operator<(const CompoundMinMax& lhs, const CompoundMinMax& rhs) {
    return lhs.roots < rhs.roots;
}
inline bool operator!=(const CompoundMinMax& lhs, const CompoundMinMax& rhs) {
    return !(lhs == rhs);
}
inline std::ostream& operator<<(std::ostream& os, const CompoundMinMax& data) {
    os << "min-max(" << data.roots << ")";
    return os;
}

/**
 * Represents the maximum function  of the contained indexed root functions.
 */
struct CompoundMaxMin {
    std::vector<std::vector<IndexedRoot>> roots;
    void polys(boost::container::flat_set<PolyRef>& result) const {
        for (const auto& r : roots) {
            for (const auto& r1 : r) {
                result.insert(r1.poly);
            }
        }
    }
    std::optional<PiecewiseLinearInfo> bounds;
};
inline bool operator==(const CompoundMaxMin& lhs, const CompoundMaxMin& rhs) {
    return lhs.roots == rhs.roots;
}
inline bool operator<(const CompoundMaxMin& lhs, const CompoundMaxMin& rhs) {
    return lhs.roots < rhs.roots;
}
inline bool operator!=(const CompoundMaxMin& lhs, const CompoundMaxMin& rhs) {
    return !(lhs == rhs);
}
inline std::ostream& operator<<(std::ostream& os, const CompoundMaxMin& data) {
    os << "max-min(" << data.roots << ")";
    return os;
}

class RootFunction {
    std::variant<IndexedRoot, CompoundMinMax, CompoundMaxMin> m_data;

public: 
    RootFunction(IndexedRoot data) : m_data(data) {}; 
    RootFunction(CompoundMinMax&& data) : m_data(data) {}; 
    RootFunction(CompoundMaxMin&& data) : m_data(data) {};
    bool is_root() const { return std::holds_alternative<IndexedRoot>(m_data); }
    bool is_cminmax() const { return std::holds_alternative<CompoundMinMax>(m_data); }
    bool is_cmaxmin() const { return std::holds_alternative<CompoundMaxMin>(m_data); }
    const IndexedRoot& root() const { return std::get<IndexedRoot>(m_data); }
    const CompoundMinMax& cminmax() const { return std::get<CompoundMinMax>(m_data); }
    const CompoundMaxMin& cmaxmin() const { return std::get<CompoundMaxMin>(m_data); }

    const auto& roots() const {
        assert(!is_root());
        return is_cminmax() ? cminmax().roots : cmaxmin().roots;
    }

    void polys(boost::container::flat_set<PolyRef>& result) const {
        if (std::holds_alternative<IndexedRoot>(m_data)) {
            result.insert(std::get<IndexedRoot>(m_data).poly);
        } else if (std::holds_alternative<CompoundMinMax>(m_data)) {
            std::get<CompoundMinMax>(m_data).polys(result);
        } else if (std::holds_alternative<CompoundMaxMin>(m_data)) {
            std::get<CompoundMaxMin>(m_data).polys(result);
        }
    }

    boost::container::flat_set<PolyRef> polys() const {
        boost::container::flat_set<PolyRef> result;
        polys(result);
        return result;
    }

    bool has_poly(const PolyRef poly) const {
        if (is_root()) {
            return root().poly == poly;
        } else if (is_cmaxmin()) {
            auto it = std::find_if(cmaxmin().roots.begin(), cmaxmin().roots.end(), [&poly](const auto& roots) {
                return std::find_if(roots.begin(), roots.end(), [&poly](const auto& root) { return root.poly == poly;}) != roots.end();
            });
            return !(it == cmaxmin().roots.end());
        } else if (is_cminmax()) {
            auto it = std::find_if(cminmax().roots.begin(), cminmax().roots.end(), [&poly](const auto& roots) {
                return std::find_if(roots.begin(), roots.end(), [&poly](const auto& root) { return root.poly == poly;}) != roots.end();
            });
            return !(it == cminmax().roots.end());
        } else {
            assert(false);
            return false;
        }
    }

    std::optional<IndexedRoot> poly_root_below(const PolyRef poly) const {
        if (is_root() && root().poly == poly) {
            return root();
        } else if (is_cmaxmin()) {
            auto it = std::find_if(cmaxmin().roots.begin(), cmaxmin().roots.end(), [&poly](const auto& roots) { return roots.size() == 1 && roots[0].poly == poly;;});
            if (it == cmaxmin().roots.end()) return std::nullopt;
            else return *it->begin();
        } else {
            return std::nullopt;
        }
    };

    std::optional<IndexedRoot> poly_root_above(const PolyRef poly) const {
        if (is_root() && root().poly == poly) {
            return root();
        } else if (is_cminmax()) {
            auto it = std::find_if(cminmax().roots.begin(), cminmax().roots.end(), [&poly](const auto& roots) { return roots.size() == 1 && roots[0].poly == poly;;});
            if (it == cminmax().roots.end()) return std::nullopt;
            else return *it->begin();
        } else {
            return std::nullopt;
        }
    };

    friend bool operator==(const RootFunction& lhs, const RootFunction& rhs);
    friend bool operator<(const RootFunction& lhs, const RootFunction& rhs);
    friend std::ostream& operator<<(std::ostream& os, const RootFunction& data);
};
inline bool operator==(const RootFunction& lhs, const RootFunction& rhs) {
    return lhs.m_data == rhs.m_data;
}
inline bool operator<(const RootFunction& lhs, const RootFunction& rhs) {
    return lhs.m_data < rhs.m_data;
}
inline bool operator!=(const RootFunction& lhs, const RootFunction& rhs) {
    return !(lhs == rhs);
}
inline std::ostream& operator<<(std::ostream& os, const RootFunction& data) {
    os << data.m_data;
    return os;
}


/// Bound type of a SymbolicInterval.
class Bound {
    enum class Type { infty, strict, weak };
    Type m_type;
    std::optional<RootFunction> m_value;
    Bound(Type type, std::optional<RootFunction> value) : m_type(type), m_value(value) {}

public:
    static Bound infty() {
        return Bound(Type::infty, std::nullopt);
    }
    static Bound strict(RootFunction value) {
        return Bound(Type::strict, value);
    }    
    static Bound weak(RootFunction value) {
        return Bound(Type::weak, value);
    }

    bool is_infty() const {
        return m_type == Type::infty;
    }
    bool is_strict() const {
        return m_type == Type::strict;
    }
    bool is_weak() const {
        return m_type == Type::weak;
    }
    const RootFunction& value() const {
        return *m_value;
    }

    void set_weak() {
        if (is_strict()) m_type = Type::weak;
    }

    bool operator==(const Bound& other) const {
        return m_type == other.m_type && m_value == other.m_value;
    }

    bool operator!=(const Bound& other) const {
        return !(*this == other);
    }
};
/**
 * A symbolic interal whose bounds are defined by indexed root expressions. Bounds can be infty, strict or weak. A special case is a section where the lower and upper bound are equal and weak.
 */
class SymbolicInterval {
    Bound m_lower;
    Bound m_upper;

public:
    /**
     * Constructs a section.
     */
    SymbolicInterval(IndexedRoot root) : m_lower(Bound::weak(root)), m_upper(Bound::weak(root)) {}
    /**
     * Constructs an interval with arbitrary bounds.
     */
    SymbolicInterval(Bound lower, Bound upper) : m_lower(lower), m_upper(upper) {
        assert(lower != upper || !(lower.is_strict() && upper.is_strict()));
    }
    /**
     * Constructs (-oo, oo).
     */
    SymbolicInterval() : m_lower(Bound::infty()), m_upper(Bound::infty()) {}

    bool is_section() const {
        return m_lower == m_upper && m_lower.is_weak();
    }

    /**
     * In case of a section, the defining indexed root is returned.
     */
    const IndexedRoot& section_defining() const {
        assert(is_section());
        return m_lower.value().root();
    }

    /**
     * Return the lower bound.
     */
    const auto& lower() const {
        return m_lower;
    }

    /**
     * Returns the upper bound.
     */
    const auto& upper() const {
        return m_upper;
    }

    void polys(boost::container::flat_set<PolyRef>& result) const {
        if (!m_lower.is_infty()) {
            m_lower.value().polys(result);
        }
        if (!m_upper.is_infty()) {
            m_upper.value().polys(result);
        }
    }

    boost::container::flat_set<PolyRef> polys() const {
        boost::container::flat_set<PolyRef> result;
        polys(result);
        return result;
    }

    void set_to_closure() {
        m_lower.set_weak();
        m_upper.set_weak();
    }
};
inline std::ostream& operator<<(std::ostream& os, const SymbolicInterval& data) {
    if (data.is_section()) {
        os << "[" << data.section_defining() << "]";
    } else {
        if (data.lower().is_infty()) {
            os << "(-oo";
        } else if (data.lower().is_weak()) {
            os << "[" << data.lower().value();
        } else if (data.lower().is_strict()) {
            os << "(" << data.lower().value();
        }
        os << ", ";
        if (data.upper().is_infty()) {
            os << "oo)";
        } else if (data.upper().is_weak()) {
            os << data.upper().value() << "]";
        } else if (data.upper().is_strict()) {
            os << data.upper().value() << ")";
        }
    }
    return os;
}

/**
 * Describes a covering of the real line by SymbolicIntervals (given an appropriate sample).
 */
class CoveringDescription {
    std::vector<SymbolicInterval> m_data;

public:
    /**
     * Add a SymbolicInterval to the covering.
     * 
     * The added cell needs to be the rightmost cell of the already added cells and not be contained in any of these cells (or vice versa).
     * 
     * * The first cell needs to have -oo as left bound.
     * * The last cell needs to have oo as right bound.
     * * All cells need to cover the real line under an appropriate sample.
     * * Evaluated under an appropriate sample, the left bound of the added cell c is strictly greater than the left bounds of already added cells (considering also "strictness" of the bounds).
     * * The right bound of the added cell c needs to be greater than all right bounds of already added cells (considering also "strictness" of the bounds).
     */
    void add(const SymbolicInterval& c) {
        assert(!m_data.empty() || (!c.is_section() && c.lower().is_infty()));
        assert(m_data.empty() || c.is_section() || !c.lower().is_infty());
        assert(m_data.empty() || m_data.back().is_section() || !m_data.back().upper().is_infty());
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
 * A relation between two roots.
 * 
 */
struct IndexedRootRelation {
    RootFunction first;
    RootFunction second;
    bool is_strict;
};
inline bool operator==(const IndexedRootRelation& lhs, const IndexedRootRelation& rhs) {
    return lhs.first == rhs.first && lhs.second == rhs.second && lhs.is_strict == rhs.is_strict;
}
inline bool operator<(const IndexedRootRelation& lhs, const IndexedRootRelation& rhs) {
    return lhs.first < rhs.first || (lhs.first == rhs.first &&  lhs.second < rhs.second) || (lhs.first == rhs.first &&  lhs.second == rhs.second && lhs.is_strict < rhs.is_strict);
}
inline std::ostream& operator<<(std::ostream& os, const IndexedRootRelation& data) {
    os << "(";
    os << data.first;
    if (data.is_strict) os << " < ";
    else os << " <= ";
    os << data.second;
    os << ")";
    return os;
}
/**
 * Describes an ordering of IndexedRoots.
 */
class IndexedRootOrdering {
    boost::container::flat_map<RootFunction, boost::container::flat_set<RootFunction>> m_leq;
    boost::container::flat_map<RootFunction, boost::container::flat_set<RootFunction>> m_geq;
    boost::container::flat_map<RootFunction, boost::container::flat_set<RootFunction>> m_less;
    boost::container::flat_map<RootFunction, boost::container::flat_set<RootFunction>> m_greater;
    
    std::vector<IndexedRootRelation> m_data;

    boost::container::flat_map<datastructures::PolyRef, boost::container::flat_set<datastructures::PolyRef>> m_poly_pairs;

    bool m_is_projective = false;

    void add_poly_pair(PolyRef p1, PolyRef p2) {
        m_poly_pairs.try_emplace(p1).first->second.insert(p2);
        m_poly_pairs.try_emplace(p2).first->second.insert(p1);
    }

public:
    std::optional<SymbolicInterval> biggest_cell_wrt; // a hack, stores which cell is described by this ordering

    void add_leq(RootFunction first, RootFunction second) {
        //assert(first.poly.level == second.poly.level);
        if (first != second) {
            m_data.push_back(IndexedRootRelation{first, second, false});
            if (!m_leq.contains(first)) m_leq.emplace(first, boost::container::flat_set<RootFunction>());
            m_leq[first].insert(second);
            if (!m_geq.contains(second)) m_geq.emplace(second, boost::container::flat_set<RootFunction>());
            m_geq[second].insert(first);

            if (first.is_root() && second.is_root()) {
                add_poly_pair(first.root().poly, second.root().poly);
            }
        }
    }

    void add_less(RootFunction first, RootFunction second) {
        //assert(first.poly.level == second.poly.level);
        assert(first != second);
        m_data.push_back(IndexedRootRelation{first, second, true});
        if (!m_less.contains(first)) m_less.emplace(first, boost::container::flat_set<RootFunction>());
        m_less[first].insert(second);
        if (!m_greater.contains(second)) m_greater.emplace(second, boost::container::flat_set<RootFunction>());
        m_greater[second].insert(first);

        if (first.is_root() && second.is_root()) {
            add_poly_pair(first.root().poly, second.root().poly);
        }
    }

    void add_eq(RootFunction first, RootFunction second) {
        //assert(first.poly.level == second.poly.level);
        if (first == second) return;
        add_leq(first, second);
        add_leq(second, first);
    }

    const auto& data() const {
        return m_data;
    }

    const auto& leq() const {
        return m_leq;
    }

    const auto& geq() const {
        return m_leq;
    }

    bool holds_transitive(RootFunction first, RootFunction second, bool strict) const {
        boost::container::flat_set<RootFunction> reached({first});
        std::vector<RootFunction> active({first});
        if (first == second) return true;
        while(!active.empty()) {
            auto current = active.back();
            active.pop_back();
            if (!strict && m_leq.contains(current)) {
                for (const auto& e : m_leq.at(current)) {
                    if (!reached.contains(e)) {
                        if (e == second) return true;
                        reached.insert(e);
                        active.push_back(e);
                    }
                }
            }
            if (m_less.contains(current)) {
                for (const auto& e : m_less.at(current)) {
                    if (!reached.contains(e)) {
                        if (e == second) return true;
                        reached.insert(e);
                        active.push_back(e);
                    }
                }
            }
        }
        return false;
    }

    std::optional<RootFunction> holds_transitive(RootFunction first, PolyRef poly, bool strict) const {
        boost::container::flat_set<RootFunction> reached({first});
        std::vector<RootFunction> active({first});
        std::optional<RootFunction> result;
        if (first.poly_root_above(poly)) return first.poly_root_above(poly);
        while(!active.empty()) {
            auto current = active.back();
            active.pop_back();
            if (!strict && m_leq.contains(current)) {
                for (const auto& e : m_leq.at(current)) {
                    if (!reached.contains(e)) {
                        auto er = e.poly_root_above(poly);
                        if (er && (!result || result->poly_root_above(poly)->index > er->index)) result = e; 
                        reached.insert(e);
                        active.push_back(e);
                    }
                }
            }
            if (m_less.contains(current)) {
                for (const auto& e : m_less.at(current)) {
                    if (!reached.contains(e)) {
                        auto er = e.poly_root_above(poly);
                        if (er && (!result || result->poly_root_above(poly)->index > er->index)) result = e; 
                        reached.insert(e);
                        active.push_back(e);
                    }
                }
            }
        }
        return result;
    }

    std::optional<RootFunction> holds_transitive(PolyRef poly, RootFunction second, bool strict) const {
        boost::container::flat_set<RootFunction> reached({second});
        std::vector<RootFunction> active({second});
        std::optional<RootFunction> result;
        if (second.poly_root_below(poly)) return second.poly_root_below(poly);
        while(!active.empty()) {
            auto current = active.back();
            active.pop_back();
            if (!strict && m_geq.contains(current)) {
                for (const auto& e : m_geq.at(current)) {
                    if (!reached.contains(e)) {
                        auto er = e.poly_root_below(poly);
                        if (er && (!result || result->poly_root_below(poly)->index < er->index)) result = e; 
                        reached.insert(e);
                        active.push_back(e);
                    }
                }
            }
            if (m_greater.contains(current)) {
                for (const auto& e : m_greater.at(current)) {
                    if (!reached.contains(e)) {
                        auto er = e.poly_root_below(poly);
                        if (er && (!result || result->poly_root_below(poly)->index < er->index)) result = e; 
                        reached.insert(e);
                        active.push_back(e);
                    }
                }
            }
        }
        return result;
    }

    void polys(boost::container::flat_set<PolyRef>& result) const {
        for (const auto& pair : m_data) {
            pair.first.polys(result);
            pair.second.polys(result);
        }
    }

    boost::container::flat_set<PolyRef> polys() const {
        boost::container::flat_set<PolyRef> result;
        polys(result);
        return result;
    }

    const boost::container::flat_set<PolyRef>& polys(const PolyRef p) const {
        return m_poly_pairs.at(p);
    }

    bool has_pair(const PolyRef p1, const PolyRef p2) const {
        auto it = m_poly_pairs.find(p1);
        if (it == m_poly_pairs.end()) return false;
        return it->second.find(p2) != it->second.end();
    }

    void set_projective() {
        m_is_projective = true;
    }

    bool is_projective() const {
        return m_is_projective;
    }
};
inline std::ostream& operator<<(std::ostream& os, const IndexedRootOrdering& data) {
    os << data.data();
    return os;
}
inline bool operator==(const IndexedRootOrdering& a, const IndexedRootOrdering& b) {
    return a.data() == b.data();
}

}