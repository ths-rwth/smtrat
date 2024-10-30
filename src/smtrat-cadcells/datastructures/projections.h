#pragma once

#include <optional>

#include "../common.h"

#include "polynomials.h"
#include "roots.h"

#include <carl-arith/poly/ctxpoly/Functions.h>
#include <carl-arith/poly/libpoly/Functions.h>

#include <carl-arith/poly/umvpoly/MultivariatePolynomial.h>
#include <carl-arith/poly/umvpoly/functions/Derivative.h>
#include <carl-arith/poly/Conversion.h>

#include "../OCApproximationStatistics.h"
#include "../CADCellsStatistics.h"

namespace smtrat::cadcells::datastructures {

namespace detail {

struct PolyProperties {
    boost::container::flat_map<PolyRef, PolyRef> res;
    std::optional<PolyRef> disc;
    std::optional<PolyRef> ldcf;
    std::vector<PolyRef> factors_nonconst;
    boost::container::flat_map<carl::Variable, PolyRef> derivatives;
    std::size_t total_degree = 0;
    std::vector<std::size_t> monomial_total_degrees;
    std::vector<std::size_t> monomial_degrees;
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
        if (p.level-1 >= m_poly_cache.size()) {
            m_poly_cache.resize(p.level);
        }
        if (p.id >= m_poly_cache[p.level-1].size()) {
            m_poly_cache[p.level-1].resize(p.id+1);
        }
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

    // Clearing caches disabled as higher-level polynomials might still be needed (mainly in filtering):

    /// Clears all polynomials of the specified level and higher in the polynomial cache as well as their projection results.
    void clear_cache(size_t /*level*/) {
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
    void clear_assignment_cache(const Assignment& /*assignment*/) {
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
            SMTRAT_STATISTICS_CALL(statistics().projection_start());
            auto result = m_pool(carl::resultant(m_pool(p), m_pool(q)));
            assert(!is_zero(result));
            cache(p).res.emplace(q, result);
            SMTRAT_STATISTICS_CALL(statistics().projection_end());
            SMTRAT_STATISTICS_CALL(statistics().resultant(total_degree(result), degree(result), result.level));
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
            SMTRAT_STATISTICS_CALL(statistics().projection_start());
            auto result = m_pool(carl::discriminant(m_pool(p)));
            assert(!is_zero(result));
            cache(p).disc = result;
            SMTRAT_STATISTICS_CALL(statistics().projection_end());
            SMTRAT_STATISTICS_CALL(statistics().discriminant(total_degree(result), degree(result), result.level));
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
            SMTRAT_STATISTICS_CALL(statistics().projection_start());
            auto result = m_pool(m_pool(p).lcoeff());
            assert(!is_zero(result));
            cache(p).ldcf = result;
            SMTRAT_STATISTICS_CALL(statistics().projection_end());
            SMTRAT_STATISTICS_CALL(statistics().leading_coefficient(total_degree(result), degree(result), result.level));
            return result;
        }
    }

    const std::vector<PolyRef>& factors_nonconst(PolyRef p) {
        if (cache(p).factors_nonconst.empty()) {
            SMTRAT_STATISTICS_CALL(statistics().projection_start());
            for (const auto& factor : carl::irreducible_factors(m_pool(p), false)) {
                cache(p).factors_nonconst.emplace_back(m_pool(factor));
                SMTRAT_STATISTICS_CALL(statistics().factor(total_degree(m_pool(factor)), degree(m_pool(factor)), m_pool(factor).level));
            }
            SMTRAT_STATISTICS_CALL(statistics().projection_end());
        }
        return cache(p).factors_nonconst;
    }

    bool is_zero(const Assignment& sample, PolyRef p) {
        auto restricted_sample = restrict_assignment(sample, p);
        assert(p.level == level_of(restricted_sample));
        if (restricted_sample.empty()) return is_zero(p);
        if (cache(restricted_sample).is_zero.find(p) == cache(restricted_sample).is_zero.end()) {
            SMTRAT_STATISTICS_CALL(statistics().evaluate_call(restricted_sample));
            SMTRAT_STATISTICS_CALL(statistics().projection_start());
            auto mv = carl::evaluate(carl::BasicConstraint<Polynomial>(m_pool(p), carl::Relation::EQ), restricted_sample);
            assert(!indeterminate(mv));
            cache(restricted_sample).is_zero[p] = (bool) mv;
            SMTRAT_STATISTICS_CALL(statistics().projection_end());
        }
        return cache(restricted_sample).is_zero[p];
    }

    size_t num_roots(const Assignment& sample, PolyRef p) {
        assert(p.level >= level_of(sample)+1);
        assert(!carl::is_constant(m_pool(p)));
        auto restricted_sample = restrict_base_assignment(sample, p);
        assert(level_of(restricted_sample) == p.base_level);
        if (cache(restricted_sample).real_roots.find(p) == cache(restricted_sample).real_roots.end()) {
            SMTRAT_STATISTICS_CALL(statistics().real_roots_call(restricted_sample));
            SMTRAT_STATISTICS_CALL(statistics().projection_start());
            cache(restricted_sample).real_roots.emplace(p, carl::real_roots(m_pool(p), restricted_sample));
            SMTRAT_STATISTICS_CALL(statistics().projection_end());
            SMTRAT_STATISTICS_CALL(statistics().real_roots_result(cache(restricted_sample).real_roots.at(p)));
        }
        assert(cache(restricted_sample).real_roots.at(p).is_univariate());
        return cache(restricted_sample).real_roots.at(p).roots().size();
    }

    const std::vector<RAN>& real_roots(const Assignment& sample, PolyRef p) {
        //assert(p.level >= level_of(sample)+1);
        assert(!carl::is_constant(m_pool(p)));
        auto restricted_sample = restrict_base_assignment(sample, p);
        assert(level_of(restricted_sample) == p.base_level);
        if (cache(restricted_sample).real_roots.find(p) == cache(restricted_sample).real_roots.end()) {
            SMTRAT_STATISTICS_CALL(statistics().real_roots_call(restricted_sample));
            SMTRAT_STATISTICS_CALL(statistics().projection_start());
            cache(restricted_sample).real_roots.emplace(p, carl::real_roots(m_pool(p), restricted_sample));
            SMTRAT_STATISTICS_CALL(statistics().projection_end());
            SMTRAT_STATISTICS_CALL(statistics().real_roots_result(cache(restricted_sample).real_roots.at(p)));
        }
        assert(cache(restricted_sample).real_roots.at(p).is_univariate());
        return cache(restricted_sample).real_roots.at(p).roots();
    }

    const std::vector<RAN> real_roots_reducible(const Assignment& sample, PolyRef p) {
        assert(!carl::is_constant(m_pool(p)));
        auto restricted_sample = restrict_base_assignment(sample, p);
        assert(level_of(restricted_sample) == p.base_level);
        std::vector<RAN> roots;       
        for (const auto& factor : factors_nonconst(p)) {
            if (factor.level == p.level) {
                if (!is_nullified(restricted_sample, factor)) {
                    const auto& r = real_roots(restricted_sample, factor);
                    roots.insert(roots.end(), r.begin(), r.end());
                }
            }
        }
        std::sort(roots.begin(), roots.end());
        return roots;        
    }

    bool is_nullified(const Assignment& sample, PolyRef p) {
        //assert(p.level >= level_of(sample)+1);
        assert(!carl::is_constant(m_pool(p)));
        auto restricted_sample = restrict_base_assignment(sample, p);
        assert(level_of(restricted_sample) == p.base_level);
        auto poly = m_pool(p);
		if (carl::is_linear(poly)) return false;
        if (cache(restricted_sample).real_roots.find(p) == cache(restricted_sample).real_roots.end()) {
            SMTRAT_STATISTICS_CALL(statistics().real_roots_call(restricted_sample));
            SMTRAT_STATISTICS_CALL(statistics().projection_start());
            cache(restricted_sample).real_roots.emplace(p, carl::real_roots(m_pool(p), restricted_sample));
            SMTRAT_STATISTICS_CALL(statistics().projection_end());
            SMTRAT_STATISTICS_CALL(statistics().real_roots_result(cache(restricted_sample).real_roots.at(p)));
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

    std::vector<PolyRef> coeffs(PolyRef p) {
        std::vector<PolyRef> result;
        SMTRAT_STATISTICS_CALL(statistics().projection_start());
        for (const auto& coeff :  m_pool(p).coefficients()) {
            result.emplace_back(m_pool(coeff));
            SMTRAT_STATISTICS_CALL(statistics().coefficient(total_degree(m_pool(coeff)), degree(m_pool(coeff)), m_pool(coeff).level));
        }
        SMTRAT_STATISTICS_CALL(statistics().projection_end());
        return result;
    }

    bool has_const_coeff(PolyRef p) const {
        for (const auto& coeff :  m_pool(p).coefficients()) {
            if (carl::is_constant(coeff) && !carl::is_zero(coeff)) return true;
        }
        return false;
    }

    PolyRef simplest_nonzero_coeff(const Assignment& sample, PolyRef p, std::function<bool(const Polynomial&,const Polynomial&)> compare) {
        std::optional<Polynomial> result;
        SMTRAT_STATISTICS_CALL(statistics().projection_start());
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
        SMTRAT_STATISTICS_CALL(statistics().projection_end());
        SMTRAT_STATISTICS_CALL(statistics().coefficient(total_degree(m_pool(*result)), degree(m_pool(*result)), m_pool(*result).level));
        return m_pool(*result);
    }

    std::vector<carl::Variable> variables(PolyRef p) {
        return carl::variables(m_pool(p)).as_vector();
    }

    PolyRef derivative(PolyRef p, carl::Variable var) {
        if (cache(p).derivatives.find(var) != cache(p).derivatives.end()) {
            return cache(p).derivatives[var];
        } else {
            SMTRAT_STATISTICS_CALL(statistics().projection_start());
            auto input = m_pool(p);
            PolyRef result;
            if (input.main_var() == var) {
                result = m_pool(carl::derivative(input));
            } else {
                assert(input.has(var));
                result = m_pool(carl::convert<Polynomial>(m_pool.context(), carl::derivative(carl::convert<Poly>(input), var)));
            }
            // auto result = m_pool(carl::derivative(m_pool(p), var)); // not implemented
            cache(p).derivatives.emplace(var, result);
            assert(result.level <= p.level);
            SMTRAT_STATISTICS_CALL(statistics().projection_end());
            SMTRAT_STATISTICS_CALL(statistics().derivative(total_degree(result), degree(result), result.level));
            return result;
        }
    }

    std::size_t degree(PolyRef p) const {
        return m_pool(p).degree();
    }

    std::size_t total_degree(PolyRef p) {
        if (p.level == 0) return 0;
        if (cache(p).total_degree == 0) {
            cache(p).total_degree = m_pool(p).total_degree();
        }
        return cache(p).total_degree;
    }

    const std::vector<std::size_t>& monomial_total_degrees(PolyRef p) {
        if (cache(p).monomial_total_degrees.empty()) {
            cache(p).monomial_total_degrees = m_pool(p).monomial_total_degrees();
        }
        return cache(p).monomial_total_degrees;
    }

    const std::vector<std::size_t>& monomial_degrees(PolyRef p) {
        if (cache(p).monomial_degrees.empty()) {
            cache(p).monomial_degrees = m_pool(p).monomial_degrees(main_var(p));
        }
        return cache(p).monomial_degrees;
    }

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

    PolyConstraint negation(const PolyConstraint& constraint) const {
        return PolyConstraint{constraint.lhs, carl::inverse(constraint.relation)};
    }

    auto evaluate(const Assignment& ass, const PolyConstraint& constraint) {
        return carl::evaluate(polys()(constraint), ass);
    }

    auto evaluate(const Assignment& ass, const IndexedRootConstraint& constraint) {
        return carl::evaluate(ass.at(main_var(constraint.bound.poly)), constraint.relation, evaluate(ass, constraint.bound));
    }

};

}