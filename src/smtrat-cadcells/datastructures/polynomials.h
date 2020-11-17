#pragma once

#include "../common.h"
#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/model.h>
#include <carl/util/IDPool.h>

namespace smtrat::cadcells::datastructures {

struct poly_ref{
    size_t level;
    size_t id;    
};

class poly_pool {
    // TODO safe memory somehow:
    std::vector<carl::IDPool> m_id_pools;
    std::vector<std::vector<Poly>> m_polys;
    std::vector<std::map<Poly, size_t>> m_poly_ids;

public:

    poly_ref operator()(const Poly& poly) {
        poly_ref ref;
        ref.level = level_of(poly);
        auto res = m_poly_ids[ref.level-1].find(poly);
        if (res == m_poly_ids[ref.level-1].end()) {
            ref.id = m_id_pools[ref.level-1].get();
            m_poly_ids[ref.level-1].emplace(poly, ref.id);
            m_polys[ref.level-1][ref.id] = poly;
        } else {
            ref.id = *res;
        }
        return ref;
    }

    const Poly& operator()(poly_ref ref) const {
        assert(ref.level <= m_id_pools.size());
        assert(ref.id < m_polys[ref.level-1].size());
        return m_polys[ref.level-1][ref.id];
    }

    void clear_level(size_t level) {
        m_id_pools[level-1].clear();
        m_polys[level-1].clear();
        m_poly_ids[level-1].clear();
    }
};

}