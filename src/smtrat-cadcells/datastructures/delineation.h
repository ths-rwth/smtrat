#pragma once

#include <map>
#include <vector>
#include <boost/container/flat_set.hpp>
namespace smtrat::cadcells::datastructures {

using RootMap = std::map<RAN, std::vector<IndexedRoot>>;

class DelineationInterval {
    RootMap::const_iterator m_lower;
    RootMap::const_iterator m_upper;
    RootMap::const_iterator m_end;

    DelineationInterval(RootMap::const_iterator&& lower, RootMap::const_iterator&& upper, RootMap::const_iterator&& end) : m_lower(lower), m_upper(upper), m_end(end) {};

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
};    
std::ostream& operator<<(std::ostream& os, const DelineationInterval& data) {
    if (data.is_section()) {
        os << "[" << *data.lower() << ", " << *data.upper() << "]";
    } else if (!data.lower_unbounded() && !data.upper_unbounded()) {
        os << "(" << *data.lower() << ", " << *data.upper() << ")";
    } else if (!data.lower_unbounded()) {
        os << "(" << *data.lower() << ", oo)";
    } else if (!data.upper_unbounded()) {
        os << "(-oo, " << *data.upper() << ")";
    } else {
        os << "(-oo, oo)";
    }
    return os;
}

class Delineation {
    friend class DelineationInterval;

    RootMap m_roots;
    boost::container::flat_set<PolyRef> m_polys_nullified;
    boost::container::flat_set<PolyRef> m_polys_noroot;

public: 
    Delineation() {}

    const auto& roots() const {
        return m_roots;
    }
    const auto& nullified() const {
        return m_polys_nullified;
    }
    const auto& nonzero() const {
        return m_polys_noroot;
    }
    bool empty() const {
        return m_roots.empty() && m_polys_nullified.empty() && m_polys_noroot.empty();
    }

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

        return DelineationInterval(std::move(lower),std::move(upper),std::move(m_roots.end()));
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
std::ostream& operator<<(std::ostream& os, const Delineation& data) {
    os << "(roots: " << data.roots() << "; nonzero: " << data.nonzero() << "; nullified: "  << data.nullified() << ")";
    return os;
}

bool lower_less(const DelineationInterval& del1, const DelineationInterval& del2) {
    if (del1.lower_unbounded()) return !del2.lower_unbounded();
    else if (del2.lower_unbounded()) return false;
    else if (del1.lower()->first == del2.lower()->first) return del1.is_section() && del2.is_sector();
    else return del1.lower()->first < del2.lower()->first;
}

bool lower_equal(const DelineationInterval& del1, const DelineationInterval& del2) {
    if (del1.lower_unbounded() && del2.lower_unbounded()) return true;
    else if (del1.lower_unbounded() != del2.lower_unbounded()) return false;
    else if (del1.lower()->first == del2.lower()->first) return del1.is_section() == del2.is_section();
    else return false;
}

bool upper_less(const DelineationInterval& del1, const DelineationInterval& del2) {
    if (del1.upper_unbounded()) return false;
    else if (del2.upper_unbounded()) return !del1.upper_unbounded();
    else if (del1.upper()->first == del2.upper()->first) return del1.is_sector() && del2.is_section();
    else return del1.upper()->first < del2.upper()->first;
}


} 