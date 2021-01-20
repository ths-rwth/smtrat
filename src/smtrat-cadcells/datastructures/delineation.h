#pragma once

#include <map>
#include <vector>
#include <boost/container/flat_set.hpp>
namespace smtrat::cadcells::datastructures {

using root_map = std::map<ran, std::vector<indexed_root>>;

class delineation_cell { // TODO rename
    root_map::const_iterator m_lower;
    root_map::const_iterator m_upper;
    root_map::const_iterator m_end;

    delineation_cell(root_map::const_iterator&& lower, root_map::const_iterator&& upper, root_map::const_iterator&& end) : m_lower(lower), m_upper(upper), m_end(end) {};

    friend class delineation;

public:
    const bool is_section() const {
        return m_lower != m_end && m_upper != m_end && m_lower == m_upper;
    }

    const auto& lower() const {
        assert(m_lower != m_end);
        return m_lower;
    }
    const bool lower_unbounded() const {
        return m_lower != m_end;
    }

    const auto& upper() const {
        assert(m_upper != m_end);
        return m_upper;
    }
    const bool upper_unbounded() const {
        return m_upper != m_end;
    }
};    

class delineation {
    friend class delineation_cell;

    root_map m_roots;
    boost::container::flat_set<poly_ref> m_polys_nullified;
    boost::container::flat_set<poly_ref> m_polys_noroot;

public: 
    delineation() {}

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

    auto delineate_cell(const ran& sample) const {
        root_map::const_iterator lower;
        root_map::const_iterator upper;

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

        return delineation_cell(std::move(lower),std::move(upper),std::move(m_roots.end()));
    }

    void add_root(ran&& root, indexed_root&& ir_root) {
        auto irs = m_roots.find(root);
        if (irs == m_roots.end()) {
            irs = m_roots.emplace(std::move(root), std::vector<indexed_root>()).first;
        }
        auto loc = std::find(irs->second.begin(), irs->second.end(), ir_root);
        if (loc == irs->second.end()) {
            irs->second.push_back(std::move(ir_root));
        }
    }

    void add_poly_noroot(poly_ref poly) {
        m_polys_noroot.insert(poly);
    }

    void add_poly_nullified(poly_ref poly) {
        m_polys_nullified.insert(poly);
    }
};

bool lower_less(const delineation_cell& del1, const delineation_cell& del2) {
    if (del1.lower_unbounded()) return !del2.lower_unbounded();
    else if (del2.lower_unbounded()) return false;
    else if (del1.lower()->first < del2.lower()->first) return true;
    else if (del1.lower()->first == del2.lower()->first) return del1.is_section() && !del2.is_section();
    else return false;
}

bool lower_equal(const delineation_cell& del1, const delineation_cell& del2) {
    if (del1.lower_unbounded() && del2.lower_unbounded()) return true;
    else if (del1.lower()->first != del2.lower()->first) return false;
    else return del1.is_section() && del2.is_section();
}

bool upper_less(const delineation_cell& del1, const delineation_cell& del2) {
    if (del1.upper_unbounded()) return !del2.lower_unbounded();
    else if (del2.upper_unbounded()) return true;
    else if (del1.upper()->first < del2.upper()->first) return true;
    else if (del1.upper()->first == del2.upper()->first) return del1.is_section() && !del2.is_section();
    else return false;
}


} 