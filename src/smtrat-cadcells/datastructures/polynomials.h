#pragma once

#include "../common.h"
#include <smtrat-common/smtrat-common.h>
#include <carl-common/memory/IDPool.h>


namespace smtrat::cadcells::datastructures {

/**
 * Refers to a polynomial. 
 */
struct PolyRef {
    /// The level of the polynomial.
    size_t level;
    /// The id of the polynomial with respect to its level.
    size_t id;    
};
inline bool operator<(const PolyRef& lhs, const PolyRef& rhs) {
    return lhs.level < rhs.level  || (lhs.level == rhs.level && lhs.id < rhs.id);
}
inline bool operator==(const PolyRef& lhs, const PolyRef& rhs) {
    return lhs.level == rhs.level && lhs.id == rhs.id;
}
inline bool operator!=(const PolyRef& lhs, const PolyRef& rhs) {
    return !(lhs == rhs);
}

inline std::ostream& operator<<(std::ostream& os, const PolyRef& data) {
    os << "(" << data.level << " " << data.id << ")";
    return os;
}

/**
 * A pool for polynomials.
 * 
 * The polynomials are stored in a table, that is, a list of lists of polynomials of a given level.
 */
class PolyPool {
    Polynomial::ContextType m_context;
    const VariableOrdering& m_var_order;

    // TODO later: safe memory with boost::intrusive
    // std::vector<carl::IDPool> m_id_pools;
    std::vector<std::vector<Polynomial>> m_polys;
    std::vector<std::map<Polynomial, size_t>> m_poly_ids;

    inline PolyRef negative_poly_ref() const { return PolyRef {0, 0}; }
    inline PolyRef zero_poly_ref() const { return PolyRef {0, 1}; }
    inline PolyRef positive_poly_ref() const { return PolyRef {0, 2}; }
    Polynomial negative_poly;
    Polynomial zero_poly;
    Polynomial positive_poly;

public:
    /**
     * Constructs a polynomial pool with respect to a variable ordering.
     * 
     * @param var_order The variable ordering determining polynomial levels.
     */
    PolyPool(const Polynomial::ContextType& context) : m_context(context), m_var_order(context.variable_order()), negative_poly(Polynomial(m_context, -1)), zero_poly(Polynomial(m_context, 0)), positive_poly(Polynomial(m_context, 1)) {
        for (size_t i = 0; i < m_var_order.size(); i++) {
            // m_id_pools.emplace_back();
            m_polys.emplace_back();
            m_poly_ids.emplace_back();
        }
    }

    const VariableOrdering& var_order() const { return m_var_order; }

    PolyRef insert(const Polynomial& poly) {
        auto npoly = poly.normalized();
        PolyRef ref;
        ref.level = carl::level_of(npoly);
        if (ref.level == 0) {
            assert(carl::is_constant(poly));
            if (carl::is_zero(poly)) return zero_poly_ref();
            else if (carl::is_negative(poly.constant_part())) return negative_poly_ref();
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

    PolyRef operator()(const Polynomial& poly) {
        return insert(poly);
    }

    const Polynomial& get(const PolyRef& ref) const {
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

    const Polynomial& operator()(const PolyRef& ref) const {
        return get(ref);
    }

    bool known(const Polynomial& poly) const {
        auto npoly = poly.normalized();
        auto level = carl::level_of(npoly);
        auto res = m_poly_ids[level-1].find(npoly);
        return res != m_poly_ids[level-1].end();
    }

    void clear_levels(size_t level) {
        assert(level > 0);
        assert(level <= m_polys.size());
        // m_id_pools[level-1].clear();
        m_polys.erase(m_polys.begin() + (level - 1), m_polys.end());
        m_poly_ids.erase(m_poly_ids.begin() + (level - 1), m_poly_ids.end());
    }
};

}