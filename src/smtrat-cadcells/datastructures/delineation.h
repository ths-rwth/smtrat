#pragma once

namespace smtrat::cadcells::datastructures {

class delineation {
    using root_map = std::map<ran, std::vector<indexed_root>>;

    carl::Variable m_main_var;
    root_map m_roots;
    boost::flat_set<poly_ref> m_polys_nullified;
    boost::flat_set<poly_ref> m_polys_noroot;
    std::optional<root_map::const_iterator> m_lower;
    std::optional<root_map::const_iterator> m_upper;

public: 

    delineation(carl::Variable main_var) : m_main_var(main_var) {}

    const main_var() const {
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

    const auto& section() const {
        assert(m_lower && *m_lower != m_roots.end());
        return *m_lower;
    }

    const auto& lower() const {
        assert(m_lower && m_upper && *m_lower != m_roots.end());
        return *m_lower;
    }
    const bool lower_unbounded() const {
        assert(m_lower && m_upper);
        return *m_lower != m_roots.end();
    }

    const auto& upper() const {
        assert(m_lower && m_upper && *m_upper != m_roots.end());
        return *m_upper;
    }
    const bool upper_unbounded() const {
        assert(m_lower && m_upper);
        return *m_upper != m_roots.end();
    }

    void set_sample(const ran& sample) {
        if (m_roots.empty()) {
            m_lower = m_roots.end()
            m_upper = m_roots.end()
        } else {
            auto section = m_roots.find(sample);
            if (section != m_roots.end()) {
                m_lower = section;
            } else {
                m_upper = ordering.roots().upper_bound(sample);
                if (m_upper == ordering.roots().begin()) {
                    m_lower = m_roots.end();
                } else {
                    m_lower = m_upper-1;
                }
            }
        }
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

    /*
    void remove_root(ran& root, indexed_root& ir_root) {
        assert(!m_lower);
        assert(proj.main_var(ir_root.poly) == m_main_var);
        auto irs = m_roots.find(root);
        if (irs != m_roots.end()) {
            auto loc = std::find(irs->begin(), irs->end(), ir_root);
            if (loc != irs->end()) {
                if (irs->size() == 1) {
                    m_roots.erase(root);
                } else {
                    std::swap(loc, irs->back());
                    irs->pop_back();
                }
            }
        }
    }
    */

    void add_poly_noroot(poly_ref poly) {
        m_polys_noroot.insert(poly);
    }

    void add_poly_nullified(poly_ref poly) {
        m_polys_nullified.insert(poly);
    }

    /*
    void add_poly(projections& proj, poly_ref poly) {
        assert(proj.main_var(poly) == m_main_var);
        if (proj.is_nullified(poly)) {
            m_polys_nullified.insert(poly);
        } else {
            auto roots = proj.real_roots(sample, poly);
            if (roots.empty()) {
                m_polys_noroot.insert(poly);
            } else {
                for (size_t idx = 0; idx < roots.size(); idx++) {
                    add_root(roots[idx], indexed_root(poly, idx));
                }
            }
        }
    }

    void remove_poly(projections& proj, poly_ref poly) {
        assert(proj.main_var(poly) == m_main_var);
        if (!m_polys_nullified.erase(poly) && !m_polys_noroot.erase(poly)) {
            auto roots = proj.real_roots(sample, poly);
            for (size_t idx = 0; idx < roots.size(); idx++) {
                remove_root(roots[idx], indexed_root(poly, idx));
            }
        }
    }
    */
};

} 