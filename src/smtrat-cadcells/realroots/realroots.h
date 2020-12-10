#pragma once

namespace smtrat::cadcells::realroots {

std::vector<poly_ref> section_defining_polynomials(projections& proj, const Model& sample, const std::vector<poly_ref>& polys) {
    std::vector<poly_ref> results;
    for (const auto poly : polys) {
        if (proj.is_zero(sample, poly)) {
            results.emplace_back(poly);
        }
    }
    return results;
}

indexed_root section_defining_root(projections& proj, const Model& sample, const poly_ref poly) {
    auto roots = proj.real_roots(sample, poly);
    for (size_t idx = 0; idx < roots.size(); idx++) {
        if (root == sample.at(proj.main_var(poly))) {
            results.emplace_back(poly, idx);
            break;
        }
    }
}

class root_ordering {
    carl::Variable m_main_var;
    std::map<ran, std::vector<indexed_root>> m_roots;

public: 

    root_ordering(carl::Variable main_var) : m_main_var(main_var) {}

    const main_var() const {
        return m_main_var;
    }

    const auto& roots() const {
        return m_roots;
    }

    void add_root(ran&& root, indexed_root&& ir_root) {
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

    void remove_root(ran& root, indexed_root& ir_root) {
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

    void add_poly(projections& proj, poly_ref poly) {
        assert(proj.main_var(poly) == m_main_var);
        auto roots = proj.real_roots(sample, poly);
        for (size_t idx = 0; idx < roots.size(); idx++) {
            add_root(roots[idx], indexed_root(poly, idx));
        }
    }

    void remove_poly(projections& proj, poly_ref poly) {
        assert(proj.main_var(poly) == m_main_var);
        auto roots = proj.real_roots(sample, poly);
        for (size_t idx = 0; idx < roots.size(); idx++) {
            remove_root(roots[idx], indexed_root(poly, idx));
        }
    }

};

auto section(projections& proj, const Model& sample, const root_ordering& ordering) {
    return ordering.roots().find(sample[ordering.main_var()]);
}

std::pair<,> sector(projections& proj, const Model& sample, const root_ordering& ordering) {
    if (ordering.roots().empty()) {
        return std::make_pair(, );
    } else {
        auto ub = ordering.roots().upper_bound(sample[ordering.main_var()]);
        assert(ub == ordering.roots().begin() || ub-1 != sample[ordering.main_var()]);
        if (ub == ordering.roots().begin()) {

        } else if (ub == ordering.roots().end()) {

        } else {

        }
    }
}


struct delineation {
    // TODO consists of root ordering, boundaries as pointers into ordering, nonzero polys OR set of vectors
    // TODO vanishing polys
};

delineation generate_cell_delineation(projections& proj, const Model& sample, const std::vector<poly_ref>& polys) {

}

delineation generate_delineation(projections& proj, const Model& sample, const std::vector<poly_ref>& polys) {

}

struct representative {
    
};



} 