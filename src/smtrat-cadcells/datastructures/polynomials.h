#pragma once

#include "../common.h"
#include "../helper.h"
#include <smtrat-common/smtrat-common.h>
#include <carl/util/IDPool.h>


namespace smtrat::cadcells::datastructures {

struct poly_ref {
    size_t level;
    size_t id;    
};
bool operator<(const poly_ref& lhs, const poly_ref& rhs) {
    return lhs.level < rhs.level  || (lhs.level == rhs.level && lhs.id < rhs.id);
}
bool operator==(const poly_ref& lhs, const poly_ref& rhs) {
    return lhs.level == rhs.level && lhs.id == rhs.id;
}
bool operator!=(const poly_ref& lhs, const poly_ref& rhs) {
    return !(lhs == rhs);
}

std::ostream& operator<<(std::ostream& os, const poly_ref& data) {
    os << "(" << data.level << " " << data.id << ")";
    return os;
}

// TODO later: make polynomials univariate

class poly_pool {
    const variable_ordering& m_var_order;

    // TODO later: safe memory
    // std::vector<carl::IDPool> m_id_pools;
    std::vector<std::vector<Poly>> m_polys;
    std::vector<std::map<Poly, size_t>> m_poly_ids;

public:

    poly_pool(const variable_ordering& var_order) : m_var_order(var_order) {
        for (size_t i = 0; i < var_order.size(); i++) {
            // m_id_pools.emplace_back();
            m_polys.emplace_back();
            m_poly_ids.emplace_back();
        }
    }

    const variable_ordering& var_order() const { return m_var_order; }

    poly_ref operator()(const Poly& poly) {
        auto npoly = poly.normalize();
        poly_ref ref;
        ref.level = helper::level_of(m_var_order, npoly);
        assert(ref.level <= m_polys.size());
        auto res = m_poly_ids[ref.level-1].find(npoly);
        if (res == m_poly_ids[ref.level-1].end()) {
            ref.id = m_polys[ref.level-1].size(); // = m_id_pools[ref.level-1].get();
            m_poly_ids[ref.level-1].emplace(npoly, ref.id);
            m_polys[ref.level-1].push_back(npoly); // [ref.id] = npoly;
        } else {
            ref.id = res->second;
        }
        return ref;
    }

    const Poly& operator()(poly_ref ref) const {
        assert(ref.level <= m_polys.size());
        assert(ref.id < m_polys[ref.level-1].size());
        return m_polys[ref.level-1][ref.id];
    }

    bool known(const Poly& poly) const {
        auto npoly = poly.normalize();
        auto level = helper::level_of(m_var_order, npoly);
        auto res = m_poly_ids[level-1].find(npoly);
        return res != m_poly_ids[level-1].end();
    }

    void clear_level(size_t level) {
        // m_id_pools[level-1].clear();
        m_polys[level-1].clear();
        m_poly_ids[level-1].clear();
    }
};

}