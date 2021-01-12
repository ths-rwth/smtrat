#pragma once

#include <optional>

#include "../common.h"

#include "polynomials.h"

#include <carl/core/polynomialfunctions/Factorization.h>
#include <carl-model/evaluation/ModelEvaluation.h>

namespace smtrat::cadcells::datastructures {

    // TODO refactor ??

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

    const auto& cache(poly_ref p) const {
        assert(p.level-1 < m_cache.size());
        assert(p.id < m_cache[p.level-1].size());
        return m_cache[p.level-1][p.id];
    }

    auto as_univariate(poly_ref p) const {
        return carl::to_univariate_polynomial(m_pool(p), main_var(p));
    }

public:
    projections(poly_pool& pool) : m_pool(pool) {}

    auto& poly_pool() { return m_pool; }

    auto main_var(poly_ref p) const {
        return m_pool.var_order()[p.level];
    }

    poly_ref res(poly_ref p, poly_ref q) {
        assert(p.level == q.level && p.id != q.id);

        if (p.id > q.id) return res(q,p);
        assert(p.id < q.id);

        if (cache(p).res.f(q) != cache(p).res.end()) {
            return cache(p).res[q];
        } else {
            auto upoly = carl::resultant(as_univariate(p), as_univariate(q));
            assert(carl::is_constant(upoly));
            auto result = m_pool(Poly(upoly));
            assert(!is_zero(result));
            cache(p).res.insert(q, result);
            return result;
        }
    }

    bool know_disc(poly_ref p) const {
        return (bool) cache(p).disc;
    }

    bool known(const Poly& p) const {
        return m_pool.known(p);
    } 

    poly_ref disc(poly_ref p) {
        if (cache(p).disc) {
            return *cache(p).disc;
        } else {
            auto upoly = carl::discriminant(as_univariate(p));
            assert(carl::is_constant(upoly));
            auto result = m_pool(Poly(upoly));
            assert(!is_zero(result));
            cache(p).disc = result;
            return result;
        }
    }

    poly_ref ldcf(poly_ref p) {
        if (cache(p).ldcf) {
            return *cache(p).ldcf;
        } else {
            auto result = m_pool(m_pool(p).lcoeff(main_var(p)));
            assert(!is_zero(result));
            cache(p).ldcf = result;
            return result;
        }
    }

    size_t num_roots(const Model& sample, poly_ref p) { // TODO cache
        return carl::model::realRoots(m_pool(p), main_var(p), sample).size();
    }

    std::vector<ran> real_roots(const Model& sample, poly_ref p) { // TODO cache
        return carl::model::realRoots(m_pool(p), main_var(p), sample);
    }

    std::vector<poly_ref> factors_nonconst(poly_ref p) { // TODO cache
        std::vector<poly_ref> results;
        for (const auto& factor : carl::irreducibleFactors(m_pool(p), false)) {
            results.emplace_back(m_pool(factor));
        }
        return results; 
    }

    bool is_zero(const Model& sample, poly_ref p) { // TODO cache
        auto mv = carl::model::evaluate(ConstraintT(m_pool(p), carl::Relation::EQ), sample);
        assert(mv.isBool());
        return mv.asBool();
    }

    bool is_nullified(const Model& sample, poly_ref p) { // TODO cache
        auto poly = m_pool(p);
		assert(!poly.isConstant());
		if (poly.isLinear()) return false;

        std::map<carl::Variable, ran> varToRANMap;
		for (const auto& [key, value] : sample)
			varToRANMap[key.asVariable()] = value.asRAN();

		return carl::ran::interval::vanishes(as_univariate(p), varToRANMap);
    }

    bool is_ldcf_zero(const Model& sample, poly_ref p) {
        return is_zero(ldcf(p));
    }

    bool is_disc_zero(const Model& sample, poly_ref p) {
        return is_zero(disc(p));
    }

    bool is_const(poly_ref p) {
        return carl::is_constant(m_pool(p));
    }

    bool is_zero(poly_ref p) {
        return carl::is_zero(m_pool(p));
    }

    bool has_const_coeff(poly_ref p) const {
        auto poly = as_univariate(p);
        for (const auto& coeff :  poly.coefficients()) {
            if (coeff.isConstant() && !carl::isZero(coeff)) return true;
        }
        return false;
    }

    poly_ref simplest_nonzero_coeff(const Model& sample, poly_ref p, std::function<bool(const Poly&,const Poly&)> compare) const {
        std::optional<Poly> result;
        auto poly = as_univariate(p);
        for (const auto& coeff : poly.coefficients()) {
            auto mv = carl::model::evaluate(ConstraintT(coeff, carl::Relation::NEQ), sample);
            assert(mv.isBool());
            if (mv.asBool()) {
                if (!result || compare(coeff,*result)) {
                    result = coeff;
                }
            }
        }
        assert(result);
        return m_pool(*result);
    }

};

}