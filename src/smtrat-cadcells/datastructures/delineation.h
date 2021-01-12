#pragma once

#include <map>
#include <vector>
#include <boost/container/flat_set.hpp>

namespace smtrat::cadcells::datastructures {

using root_map = std::map<ran, std::vector<indexed_root>>;

class delineation {
    friend class delineation_cell;

    carl::Variable m_main_var;
    root_map m_roots;
    boost::flat_set<poly_ref> m_polys_nullified;
    boost::flat_set<poly_ref> m_polys_noroot;

public: 
    delineation(carl::Variable main_var) : m_main_var(main_var), m_lower(m_roots.end()), m_upper(m_roots.end()) {}

    const auto main_var() const {
        return m_main_var;
    }
    const auto& roots() const {
        return m_roots;
    }
    const auto& nullified() const {
        return m_polys_nullified;
    }
    const auto& noroot() const {
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
                    lower = upper-1;
                }
            }
        }

        return std::make_shared(delineation_cell(lower,upper));
    }

    void add_root(ran&& root, indexed_root&& ir_root) {
        assert(!m_lower);
        assert(proj.main_var(ir_root.poly) == m_main_var);
        auto irs = m_roots.find(root);
        if (irs == m_roots.end()) {
            irs = m_roots.emplace(std::move(root), std::vector<indexed_root>());
        }
        auto loc = std::find(irs->begin(), irs->end(), ir_root);
        if (loc == irs->end()) {
            irs->push_back(std::move(ir_root));
        }
    }

    void add_poly_noroot(poly_ref poly) {
        m_polys_noroot.insert(poly);
    }

    void add_poly_nullified(poly_ref poly) {
        m_polys_nullified.insert(poly);
    }
};

class delineation_cell {
    root_map::const_iterator m_lower;
    root_map::const_iterator m_upper;

public:
    delineation_cell(root_map::const_iterator&& lower, root_map::const_iterator&& upper) : m_lower(lower), m_upper(upper) {};

    const bool is_section() const {
        return m_lower != m_roots.end() && m_upper != m_roots.end() && m_lower == m_upper;
    }

    const auto& lower() const {
        assert(m_lower != m_roots.end());
        return m_lower;
    }
    const bool lower_unbounded() const {
        return m_lower != m_roots.end();
    }

    const auto& upper() const {
        assert(m_upper != m_roots.end());
        return m_upper;
    }
    const bool upper_unbounded() const {
        return m_upper != m_roots.end();
    }
};    

} 