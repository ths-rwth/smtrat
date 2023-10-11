#pragma once

#include <optional>

#include "../common.h"

#include "polynomials.h"
#include "roots.h"

#include <carl-arith/poly/ctxpoly/Functions.h>
#include <carl-arith/poly/libpoly/Functions.h>

#include "../OCApproximationStatistics.h"

namespace smtrat::cadcells::datastructures {

namespace detail {

struct PolyProperties {
    std::map<PolyRef, PolyRef> res;
    std::optional<PolyRef> disc;
    std::optional<PolyRef> ldcf;
    std::vector<PolyRef> factors_nonconst;
};

struct AssignmentProperties {
    std::map<PolyRef, carl::RealRootsResult<RAN>> real_roots;
    std::map<PolyRef, bool> is_zero;
};

}

/**
 * Encapsulates all computations on polynomials. 
 * Computations are cached with respect to a PolyPool.
 */
class Projections {
    PolyPool& m_pool;
    std::vector<std::vector<detail::PolyProperties>> m_poly_cache;
    std::vector<std::map<Assignment,detail::AssignmentProperties>> m_assignment_cache;

    auto& cache(PolyRef p) {
        assert(p.level > 0);
        m_poly_cache.resize(p.level);
        m_poly_cache[p.level-1].resize(p.id+1);
        return m_poly_cache[p.level-1][p.id];
    }
    const auto& cache(PolyRef p) const {
        assert(p.level > 0);
        assert(p.level-1 < m_poly_cache.size());
        assert(p.id < m_poly_cache[p.level-1].size());
        return m_poly_cache[p.level-1][p.id];
    }
    bool has_cache(PolyRef p) const {
        assert(p.level > 0);
        return (p.level-1 < m_poly_cache.size()) && (p.id < m_poly_cache[p.level-1].size());
    }

    size_t level_of(const Assignment& a) const {
        // return a.size();
        std::size_t level = m_pool.var_order().size();
        for(auto i = m_pool.var_order().rbegin(); i !=  m_pool.var_order().rend(); i++) {
            if (a.find(*i) != a.end()) return level;
            assert(level>0);
            level--;
        }
        return level;
    }

    auto& cache(const Assignment& a) {
        m_assignment_cache.resize(level_of(a)+1);
        return m_assignment_cache[level_of(a)][a];
    }
    const auto& cache(const Assignment& a) const {
        assert(level_of(a) < m_assignment_cache.size());
        assert(m_assignment_cache[level_of(a)].find(a) != m_assignment_cache[level_of(a)].end());
        return m_assignment_cache[level_of(a)].at(a);
    }

public:
    auto main_var(PolyRef p) const {
        return m_pool.var_order()[p.level-1];
    }

private:
    Assignment restrict_assignment(Assignment ass, PolyRef p) {
        auto vars = carl::variables(m_pool(p));
        // for(auto i = m_pool.var_order().rbegin(); i !=  m_pool.var_order().rend(); i++) {
        //     if (!vars.has(*i)) ass.erase(*i);
        //     else return ass;
        // }
        for (const auto var : m_pool.var_order()) {
            if (!vars.has(var)) ass.erase(var);
        }
        return ass;
    }

    Assignment restrict_base_assignment(Assignment ass, PolyRef p) {
        auto vars = carl::variables(m_pool(p));
        // for(auto i = m_pool.var_order().rbegin(); i !=  m_pool.var_order().rend(); i++) {
        //     if (!vars.has(*i) || *i == main_var(p)) ass.erase(*i);
        //     else return ass;
        // }
        for (const auto var : m_pool.var_order()) {
            if (!vars.has(var) || var == main_var(p)) ass.erase(var);
        }
        return ass;
    }

public:
    Projections(PolyPool& pool) : m_pool(pool) {}

    auto& polys() { return m_pool; }
    const auto& polys() const { return m_pool; }

    /// Clears all polynomials of the specified level and higher in the polynomial cache as well as their projection results.
    void clear_cache(size_t level) {
        return;
        // assert(level > 0);
        // m_pool.clear_levels(level);
        // if (level <= m_poly_cache.size()) {
        //     m_poly_cache.erase(m_poly_cache.begin() + (level - 1), m_poly_cache.end());
        // }
        // if (level < m_assignment_cache.size()) {
        //     m_assignment_cache.erase(m_assignment_cache.begin() + level, m_assignment_cache.end());
        // }
    }

    /// Clears all projections cached with respect to this assignment.
    void clear_assignment_cache(const Assignment& assignment) {
        return;
        // for (auto lvl = level_of(assignment); lvl < m_assignment_cache.size(); lvl++) {
        //     for (auto it = m_assignment_cache[lvl].begin(); it != m_assignment_cache[lvl].end(); ) {
        //         bool is_subset = true;
        //         for (const auto& e : it->first) {
        //             if (assignment.find(e.first) == assignment.end() || assignment.at(e.first) != e.second) {
        //                 is_subset = false;
        //                 break;
        //             }
        //         }
        //         if (is_subset) {
        //             it = m_assignment_cache[lvl].erase(it);
        //         } else {
        //             it++;
        //         }
        //     }
        // }
    }
    
    PolyRef res(PolyRef p, PolyRef q) {
        assert(p.level == q.level && p.id != q.id);

        if (p.id > q.id) return res(q,p);
        assert(p.id < q.id);

        if (cache(p).res.find(q) != cache(p).res.end()) {
            return cache(p).res[q];
        } else {
            #ifdef SMTRAT_DEVOPTION_Statistics
                OCApproximationStatistics::get_instance().resultant();
            #endif
            auto result = m_pool(carl::resultant(m_pool(p), m_pool(q)));
            assert(!is_zero(result));
            cache(p).res.emplace(q, result);
            return result;
        }
    }

    bool know_disc(PolyRef p) const {
        if (!has_cache(p)) return false;
        return (bool) cache(p).disc;
    }

    bool know_res(PolyRef p, PolyRef q) const {
        assert(p.level == q.level && p.id != q.id);
        if (p.id > q.id) return know_res(q,p);
        assert(p.id < q.id);
        if (!has_cache(p)) return false;
        return cache(p).res.find(q) != cache(p).res.end();
    }

    bool known(const Polynomial& p) const {
        return m_pool.known(p);
    } 

    PolyRef disc(PolyRef p) {
        if (cache(p).disc) {
            return *cache(p).disc;
        } else {
            #ifdef SMTRAT_DEVOPTION_Statistics
                OCApproximationStatistics::get_instance().discriminant();
            #endif
            auto result = m_pool(carl::discriminant(m_pool(p)));
            assert(!is_zero(result));
            cache(p).disc = result;
            return result;
        }
    }

    PolyRef ldcf(PolyRef p) {
        if (cache(p).ldcf) {
            return *cache(p).ldcf;
        } else {
            #ifdef SMTRAT_DEVOPTION_Statistics
                OCApproximationStatistics::get_instance().coefficient();
            #endif
            auto result = m_pool(m_pool(p).lcoeff());
            assert(!is_zero(result));
            cache(p).ldcf = result;
            return result;
        }
    }

    const std::vector<PolyRef>& factors_nonconst(PolyRef p) {
        if (cache(p).factors_nonconst.empty()) {
            for (const auto& factor : carl::irreducible_factors(m_pool(p), false)) {
                cache(p).factors_nonconst.emplace_back(m_pool(factor));
            }
        }
        return cache(p).factors_nonconst;
    }

    bool is_zero(const Assignment& sample, PolyRef p) {
        auto restricted_sample = restrict_assignment(sample, p);
        assert(p.level == level_of(restricted_sample));
        if (restricted_sample.empty()) return is_zero(p);
        if (cache(restricted_sample).is_zero.find(p) == cache(restricted_sample).is_zero.end()) {
            auto mv = carl::evaluate(carl::BasicConstraint<Polynomial>(m_pool(p), carl::Relation::EQ), restricted_sample);
            assert(!indeterminate(mv));
            cache(restricted_sample).is_zero[p] = (bool) mv;
        }
        return cache(restricted_sample).is_zero[p];
    }

    size_t num_roots(const Assignment& sample, PolyRef p) {
        assert(p.level >= level_of(sample)+1);
        assert(!carl::is_constant(m_pool(p)));
        auto restricted_sample = restrict_base_assignment(sample, p);
        assert(level_of(restricted_sample) == p.base_level);
        if (cache(restricted_sample).real_roots.find(p) == cache(restricted_sample).real_roots.end()) {
            cache(restricted_sample).real_roots.emplace(p, carl::real_roots(m_pool(p), restricted_sample));
        }
        assert(cache(restricted_sample).real_roots.at(p).is_univariate());
        return cache(restricted_sample).real_roots.at(p).roots().size();
    }

    const std::vector<RAN>& real_roots(const Assignment& sample, PolyRef p) {
        assert(p.level >= level_of(sample)+1);
        assert(!carl::is_constant(m_pool(p)));
        auto restricted_sample = restrict_base_assignment(sample, p);
        assert(level_of(restricted_sample) == p.base_level);
        if (cache(restricted_sample).real_roots.find(p) == cache(restricted_sample).real_roots.end()) {
            cache(restricted_sample).real_roots.emplace(p, carl::real_roots(m_pool(p), restricted_sample));
        }
        assert(cache(restricted_sample).real_roots.at(p).is_univariate());
        return cache(restricted_sample).real_roots.at(p).roots();
    }

    bool is_nullified(const Assignment& sample, PolyRef p) {
        assert(p.level >= level_of(sample)+1);
        assert(!carl::is_constant(m_pool(p)));
        auto restricted_sample = restrict_base_assignment(sample, p);
        assert(level_of(restricted_sample) == p.base_level);
        auto poly = m_pool(p);
		if (carl::is_linear(poly)) return false;
        if (cache(restricted_sample).real_roots.find(p) == cache(restricted_sample).real_roots.end()) {
            cache(restricted_sample).real_roots.emplace(p, carl::real_roots(m_pool(p), restricted_sample));
        }
		return cache(restricted_sample).real_roots.at(p).is_nullified();
    }

    bool is_ldcf_zero(const Assignment& sample, PolyRef p) {
        return is_zero(sample, ldcf(p));
    }

    bool is_disc_zero(const Assignment& sample, PolyRef p) {
        return is_zero(sample, disc(p));
    }

    bool is_const(PolyRef p) {
        return carl::is_constant(m_pool(p));
    }

    bool is_zero(PolyRef p) {
        return carl::is_zero(m_pool(p));
    }

    std::vector<PolyRef> coeffs(PolyRef p) const {
        std::vector<PolyRef> result;
        for (const auto& coeff :  m_pool(p).coefficients()) {
            result.emplace_back(m_pool(coeff));
        }
        return result;
    }

    bool has_const_coeff(PolyRef p) const {
        for (const auto& coeff :  m_pool(p).coefficients()) {
            if (carl::is_constant(coeff) && !carl::is_zero(coeff)) return true;
        }
        return false;
    }

    PolyRef simplest_nonzero_coeff(const Assignment& sample, PolyRef p, std::function<bool(const Polynomial&,const Polynomial&)> compare) const {
        std::optional<Polynomial> result;
        for (const auto& coeff : m_pool(p).coefficients()) {
            auto mv = carl::evaluate(carl::BasicConstraint<Polynomial>(coeff, carl::Relation::NEQ), sample);
            assert(!indeterminate(mv));
            if (mv) {
                if (!result || compare(coeff,*result)) {
                    result = coeff;
                }
            }
        }
        assert(result);
        return m_pool(*result);
    }

    std::size_t degree(PolyRef p) {
        return m_pool(p).degree();
    }

    std::size_t total_degree(PolyRef p) {
        return m_pool(p).total_degree();
    }

    // std::size_t max_degree(PolyRef p) {
    //     const auto& poly = m_pool(p);
    //     size_t deg = 0;
    //     for (const auto var : carl::variables(poly)) {
    //         deg = std::max(deg, poly.degree(var));
    //     }
    //     return deg;
    // }

        RAN evaluate(const Assignment& sample, IndexedRoot r) {
        auto roots = real_roots(sample, r.poly);
        assert(r.index <= roots.size());
        return roots[r.index-1];
    }

    inline std::pair<RAN,std::vector<datastructures::IndexedRoot>> evaluate_min(const Assignment& ass, const std::vector<datastructures::IndexedRoot>& roots) {
        std::vector<datastructures::IndexedRoot> irs;
        RAN value;
        for (const auto& root : roots) {
            auto v = evaluate(ass, root);
            if (irs.empty() || v < value) {
                irs.clear();
                irs.push_back(root);
                value = v;
            } else if (v == value) {
                irs.push_back(root);
            }
        }
        return std::make_pair(value, irs);
    }

    inline std::pair<RAN,std::vector<datastructures::IndexedRoot>> evaluate_max(const Assignment& ass, const std::vector<datastructures::IndexedRoot>& roots) {
        std::vector<datastructures::IndexedRoot> irs;
        RAN value;
        for (const auto& root : roots) {
            auto v = evaluate(ass, root);
            if (irs.empty() || v > value) {
                irs.clear();
                irs.push_back(root);
                value = v;
            } else if (v == value) {
                irs.push_back(root);
            }
        }
        return std::make_pair(value, irs);
    }

    inline std::pair<RAN,std::vector<datastructures::IndexedRoot>> evaluate(const Assignment& ass, const datastructures::CompoundMinMax& bound) {
        std::vector<datastructures::IndexedRoot> irs;
        RAN value;
        for (const auto& roots : bound.roots) {
            auto v = evaluate_max(ass, roots);
            if (irs.empty() || v.first < value) {
                irs.clear();
                irs.insert(irs.end(), v.second.begin(), v.second.end());
                value = v.first;
            } else if (v.first == value) {
                irs.insert(irs.end(), v.second.begin(), v.second.end());
            }
        }
        return std::make_pair(value, irs);
    }

    inline std::pair<RAN,std::vector<datastructures::IndexedRoot>> evaluate(const Assignment& ass, const datastructures::CompoundMaxMin& bound) {
        std::vector<datastructures::IndexedRoot> irs;
        RAN value;
        for (const auto& roots : bound.roots) {
            auto v = evaluate_min(ass, roots);
            if (irs.empty() || v.first > value) {
                irs.clear();
                irs.insert(irs.end(), v.second.begin(), v.second.end());
                value = v.first;
            } else if (v.first == value) {
                irs.insert(irs.end(), v.second.begin(), v.second.end());
            }
        }
        return std::make_pair(value, irs);
    }

    inline std::pair<RAN,std::vector<datastructures::IndexedRoot>> evaluate(const Assignment& ass, const datastructures::RootFunction& f) {
        if (f.is_root()) return std::make_pair(evaluate(ass, f.root()), std::vector<datastructures::IndexedRoot>({ f.root() }));
        else if (f.is_cminmax()) return evaluate(ass, f.cminmax());
        else if (f.is_cmaxmin()) return evaluate(ass, f.cmaxmin());
        else assert(false);
    }

};

}