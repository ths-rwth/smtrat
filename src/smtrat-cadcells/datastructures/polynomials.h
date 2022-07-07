#pragma once

#include "../common.h"
#include "../helper.h"
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

// TODO later: store carl polynomials as univariate
// TODO later: carl should be designed such that PolyAdaptor is not needed
// solution: introduce wrapper class ContextedPolynomial

template<typename P>
struct PolyAdaptor {};

template<>
struct PolyAdaptor<Poly> {
    carl::Context m_context;
    PolyAdaptor(const carl::Context& context) : m_context(context) {}
    auto negative_poly() const { return Poly(-1); }
    auto zero_poly() const { return Poly(0); }
    auto positive_poly() const { return Poly(1); }
    auto as_univariate(const Poly& p, carl::Variable v) const { return carl::to_univariate_polynomial(p, v); }
    auto as_multivariate(const carl::UnivariatePolynomial<Poly>& p) const { return Poly(p); };
    auto lcoeff(const Poly& p, carl::Variable v) const { return p.lcoeff(v); }
    std::size_t level_of(const Poly& p) const { 
        auto poly_variables = carl::variables(p).as_set();
        if (poly_variables.empty()) return 0;
        for (std::size_t level = 1; level <= m_context.variable_order().size(); ++level) {
            poly_variables.erase(m_context.variable_order()[level-1]);
            if (poly_variables.empty()) return level;
        }
        assert(false && "Poly contains variable not found in m_context.variable_order()");
        return 0;
    }
    auto main_var(const Poly& p) const {
        auto poly_variables = carl::variables(p).as_set();
        if (poly_variables.empty()) return carl::Variable::NO_VARIABLE;
        for (std::size_t level = 0; level < m_context.variable_order().size(); ++level) {
            if (poly_variables.size() == 1) return *poly_variables.begin();
            poly_variables.erase(m_context.variable_order()[level]);
        }
        assert(false && "Poly contains variable not found in m_context.variable_order()");
        return carl::Variable::NO_VARIABLE;
    }
};

template<>
struct PolyAdaptor<carl::LPPolynomial> {
    carl::LPContext m_context;
    PolyAdaptor(const carl::LPContext& context) : m_context(context) {}
    auto negative_poly() const { return carl::LPPolynomial(m_context,-1); }
    auto zero_poly() const { return carl::LPPolynomial(m_context,0); }
    auto positive_poly() const { return carl::LPPolynomial(m_context,1); }
    auto as_univariate(const carl::LPPolynomial& p, carl::Variable) const { return p; }
    auto as_multivariate(const carl::LPPolynomial& p) const { return p; };
    auto lcoeff(const carl::LPPolynomial& p, carl::Variable) const { return p.lcoeff(); }
    std::size_t level_of(const carl::LPPolynomial& p) const {
        assert(p.context() == m_context);
        if (p.is_number()) return 0;
        auto it = std::find(m_context.variable_order().begin(), m_context.variable_order().end(), p.main_var());
        assert(it != m_context.variable_order().end());
        return std::distance(m_context.variable_order().begin(), it)+1;
    }
    auto main_var(const carl::LPPolynomial& p) const { return p.main_var(); }
};


/**
 * A pool for polynomials.
 * 
 * The polynomials are stored in a table, that is, a list of lists of polynomials of a given level.
 */
class PolyPool {
    const VariableOrdering& m_var_order;
    
    PolyAdaptor<Polynomial> m_adaptor;

    // TODO later: safe memory
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
    PolyPool(const Polynomial::ContextType& context) : m_var_order(context.variable_order()), m_adaptor(context), negative_poly(m_adaptor.negative_poly()), zero_poly(m_adaptor.zero_poly()), positive_poly(m_adaptor.positive_poly()) {
        for (size_t i = 0; i < m_var_order.size(); i++) {
            // m_id_pools.emplace_back();
            m_polys.emplace_back();
            m_poly_ids.emplace_back();
        }
    }

    const VariableOrdering& var_order() const { return m_var_order; }

    const PolyAdaptor<Polynomial>& adaptor() const { return m_adaptor; }

    PolyRef insert(const Polynomial& poly) {
        auto npoly = poly.normalize();
        PolyRef ref;
        ref.level = adaptor().level_of(npoly);
        if (ref.level == 0) {
            assert(poly.is_constant());
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
        auto npoly = poly.normalize();
        auto level = adaptor().level_of(npoly);
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