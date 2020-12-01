#pragma once

#include "../common.h"
#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/model.h>

#include "polynomials.h"

namespace smtrat::cadcells::datastructures {

namespace detail {

struct poly_properties {
    std::map<poly_ref, poly_ref> res;
    std::optional<poly_ref> disc;
    std::optional<poly_ref> ldcf;
    std::optional<std::map<Model, bool>> is_zero;
    std::optional<std::map<Model, bool>> is_nullified;
    std::optional<std::map<Model, size_t>> num_roots;
};


}

/**
 * Encapsulates all computations on polynomials. 
 * Computations are cached with respect to a poly_pool.
 */
class projections {
    poly_pool& m_pool;
    std::vector<std::vector<detail::poly_properties>> m_cache;

    auto& cache(poly_ref p) {
        m_cache.resize(p.level);
        m_cache[p.level-1].resize(p.id+1);
        return m_cache[p.level-1][p.id];
    }

    auto main_var(poly_ref p) {
        return m_pool.var_order()[p.level];
    }

    auto as_univariate(poly_ref p) {
        return carl::to_univariate_polynomial(m_pool(p), main_var(p));
    }

public:
    projections(poly_pool& pool) : m_pool(pool) {}

    poly_ref res(poly_ref p, poly_ref q) {
        assert(p.level == q.level && p.id != q.id);

        if (p.id > q.id) return res(q,p);
        assert(p.id < q.id);

        if (cache(p).res.find(q) != cache(p).res.end()) {
            return cache(p).res[q];
        } else {
            auto res = m_pool(carl::resultant(as_univariate(p), as_univariate(q)));
            assert(!is_zero(res));
            cache(p).insert(q, res);
            return res;
        }
    }

    poly_ref disc(poly_ref p) {
        if (cache(p).disc) {
            return *cache(p).disc;
        } else {
            auto disc = m_pool(carl::discriminant(as_univariate(p)));
            assert(!is_zero(disc));
            cache(p).disc = disc;
            return disc;
        }
    }

    poly_ref ldcf(poly_ref p) {
        if (cache(p).ldcf) {
            return *cache(p).ldcf;
        } else {
            auto ldcf = m_pool(p).lcoeff(main_var(p));
            assert(!is_zero(ldcf));
            cache(p).ldcf = ldcf;
            return ldcf;
        }
    }

    size_t num_roots(const Model& sample, poly_ref p) {
        // TODO implement
    }

    std::vector<RealAlgebraicNumber> real_roots(const Model& sample, poly_ref p) {
        // TODO implement
    }

    // TODO cache real roots?

    bool is_zero(const Model& sample, poly_ref p) {
        // TODO implement
    }

    bool is_nullified(const Model& sample, poly_ref p) {
        // TODO implement
    }

    bool is_ldcf_zero(const Model& sample, poly_ref p) {
        return zero(ldcf(p));
    }

    bool is_disc_zero(const Model& sample, poly_ref p) {
        return zero(disc(p));
    }

    bool is_const(poly_ref p) {
        return carl::is_constant(m_pool(p));
    }

    bool is_zero(poly_ref p) {
        return carl::is_zero(m_pool(p));
    }

};

}