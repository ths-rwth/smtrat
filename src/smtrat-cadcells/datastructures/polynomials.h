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

    inline poly_ref negative_poly_ref() const { return poly_ref {0, 0}; }
    inline poly_ref zero_poly_ref() const { return poly_ref {0, 1}; }
    inline poly_ref positive_poly_ref() const { return poly_ref {0, 2}; }
    Poly negative_poly;
    Poly zero_poly;
    Poly positive_poly;

public:
    poly_pool(const variable_ordering& var_order) : m_var_order(var_order), negative_poly(-1), zero_poly(0), positive_poly(1) {
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
        if (ref.level == 0) {
            assert(poly.isConstant());
            if (carl::isZero(poly)) return zero_poly_ref();
            else if (carl::isNegative(poly.constantPart())) return negative_poly_ref();
            else return positive_poly_ref();
        }
        assert(ref.level <= m_polys.size() && ref.level > 0);
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
        if (ref.level == 0) {
            assert(ref.id <=2);
            if (ref.id == negative_poly_ref().id) return negative_poly;
            else if (ref.id == zero_poly_ref().id) return zero_poly;
            else return positive_poly;
        }
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