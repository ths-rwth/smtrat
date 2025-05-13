#pragma once

#include <smtrat-cadcells/datastructures/projections.h>

namespace smtrat::covering_ng::formula::complexity {


namespace features {

inline auto num_vars(cadcells::datastructures::Projections& proj, const Implicant& a) {
    std::vector<carl::Variable> vars;
    for (const auto& el : a) {
        auto el_vars = proj.variables(el.lhs);
        vars.insert(vars.end(), el_vars.begin(), el_vars.end());
    }
    std::sort(vars.begin(), vars.end());
    vars.erase(std::unique(vars.begin(), vars.end()), vars.end());
    return vars.size();
}

inline auto max_max_total_degree(cadcells::datastructures::Projections& proj, const Implicant& a) {
    std::size_t a_max_max_total_degree = 0;
    for (const auto& el : a) {
        a_max_max_total_degree = std::max(a_max_max_total_degree, proj.total_degree(el.lhs));
    }
    return a_max_max_total_degree;
}

inline auto sum_max_degree(cadcells::datastructures::Projections& proj, const Implicant& a) {
    std::size_t result = 0;
    for (const auto& el : a) {
        result += proj.degree(el.lhs);
    }
    return result;
}

inline auto avg_avg_degree(cadcells::datastructures::Projections& proj, const Implicant& a) {
    std::size_t sum = 0;
    std::size_t count = 0;
    for (const auto& el : a) {
        for (auto d : proj.monomial_degrees(el.lhs)) {
            sum += d;
            count++;
        }
    }
    return static_cast<double>(sum)/static_cast<double>(count);
}

inline auto sum_sum_degree(cadcells::datastructures::Projections& proj, const Implicant& a) {
    std::size_t sum = 0;
    for (const auto& el : a) {
        for (auto d : proj.monomial_degrees(el.lhs)) {
            sum += d;
        }
    }
    return sum;
}

inline auto sum_max_total_degree(cadcells::datastructures::Projections& proj, const Implicant& a) {
    std::size_t a_sum_max_total_degree = 0;
    for (const auto& el : a) {
        a_sum_max_total_degree += proj.total_degree(el.lhs);
    }
    return a_sum_max_total_degree;
}

inline auto avg_avg_total_degree(cadcells::datastructures::Projections& proj, const Implicant& a) {
    std::size_t sum = 0;
    std::size_t count = 0;
    for (const auto& el : a) {
        for (auto d : proj.monomial_total_degrees(el.lhs)) {
            sum += d;
            count++;
        }
    }
    return static_cast<double>(sum)/static_cast<double>(count);
}

inline auto sum_sum_total_degree(cadcells::datastructures::Projections& proj, const Implicant& a) {
    std::size_t sum = 0;
    for (const auto& el : a) {
        for (auto d : proj.monomial_total_degrees(el.lhs)) {
            sum += d;
        }
    }
    return sum;
}

inline auto max_level(cadcells::datastructures::Projections&, const Implicant& a) {
    cadcells::datastructures::level_t result = 0;
    for (const auto& el : a) {
        result = std::max(result, el.lhs.level);
    }
    return result;
}

inline auto sum_total_degree(cadcells::datastructures::Projections& proj, const cadcells::datastructures::PolyConstraint& a) {
    std::size_t sum = 0;
    for (auto d : proj.monomial_total_degrees(a.lhs)) {
        sum += d;
    }
    return sum;
}

inline auto product_max_total_degree(cadcells::datastructures::Projections& proj, const Implicant& a) {
    std::size_t n = 1;
    for (const auto& el: a) {
        n *= proj.total_degree(el.lhs);
    }
    return n;
}

inline auto n_nonlin(cadcells::datastructures::Projections& proj, const Implicant& a) {
    std::size_t n = 0;
    for (const auto& el: a) {
        if (proj.total_degree(el.lhs) <= 1) ++n;
    }
    return n;
}

} // namespace features

/**
 * Inspired by Pickering, Lynn, Tereso Del Rio Almajano, Matthew England, and Kelly Cohen. ‘Explainable AI Insights for Symbolic Computation: A Case Study on Selecting the Variable Ordering for Cylindrical Algebraic Decomposition’. arXiv, 29 August 2023. http://arxiv.org/abs/2304.12154.
 */
inline bool pickering_total(cadcells::datastructures::Projections& proj, const Implicant& a, const Implicant& b) {
    auto a_sum_max_degree = features::sum_max_total_degree(proj, a);
    auto b_sum_max_degree = features::sum_max_total_degree(proj, b);
    if (a_sum_max_degree != b_sum_max_degree) return a_sum_max_degree < b_sum_max_degree;
    else {
        auto a_avg_avg_degree = features::avg_avg_total_degree(proj, a);
        auto b_avg_avg_degree = features::avg_avg_total_degree(proj, b);
        if (a_avg_avg_degree != b_avg_avg_degree) return a_avg_avg_degree < b_avg_avg_degree;
        else {
            auto a_sum_sum_degree = features::sum_sum_total_degree(proj, a);
            auto b_sum_sum_degree = features::sum_sum_total_degree(proj, b);
            return a_sum_sum_degree < b_sum_sum_degree;
        }
    }
}

inline bool min_level_min_size(cadcells::datastructures::Projections& proj, const Implicant& a, const Implicant& b) {
    auto a_level = features::max_level(proj, a);
    auto b_level = features::max_level(proj, b);

    if (a_level != b_level) return a_level < b_level;
    else return a.size() < b.size();
}

inline bool min_size(cadcells::datastructures::Projections&, const Implicant& a, const Implicant& b) {
    return a.size() < b.size();
}

/**
 * Dolzmann et al 2004
 */
inline bool sotd(cadcells::datastructures::Projections& proj, const Implicant& a, const Implicant& b) {
    auto a_sum_sum_total_degree = features::sum_sum_total_degree(proj, a);
    auto b_sum_sum_total_degree = features::sum_sum_total_degree(proj, b);
    return a_sum_sum_total_degree < b_sum_sum_total_degree || (a_sum_sum_total_degree == b_sum_sum_total_degree && a.size() < b.size());
}

inline bool min_level_min_sotd(cadcells::datastructures::Projections& proj, const Implicant& a, const Implicant& b) {
    auto a_level = features::max_level(proj, a);
    auto b_level = features::max_level(proj, b);

    if (a_level != b_level) return a_level < b_level;
    else return sotd(proj, a, b);
}

inline bool min_vars_min_sotd(cadcells::datastructures::Projections& proj, const Implicant& a, const Implicant& b) {
    auto a_vars = features::num_vars(proj, a);
    auto b_vars = features::num_vars(proj, b);

    if (a_vars != b_vars) return a_vars < b_vars;
    else return sotd(proj, a, b);
}

inline bool sotd_reverse(cadcells::datastructures::Projections& proj, const Implicant& a, const Implicant& b) {
    auto a_sum_sum_total_degree = features::sum_sum_total_degree(proj, a);
    auto b_sum_sum_total_degree = features::sum_sum_total_degree(proj, b);
    return a_sum_sum_total_degree > b_sum_sum_total_degree || (a_sum_sum_total_degree == b_sum_sum_total_degree && a.size() > b.size());
}

inline bool min_max_tdeg_min_size(cadcells::datastructures::Projections& proj, const Implicant& a, const Implicant& b) {
    auto a_max_max_total_degree = features::max_max_total_degree(proj, a);
    auto b_max_max_total_degree = features::max_max_total_degree(proj, b);
    return a_max_max_total_degree < b_max_max_total_degree || (a_max_max_total_degree == b_max_max_total_degree && a.size() < b.size());
}

inline bool min_sotd(cadcells::datastructures::Projections& proj, const cadcells::datastructures::PolyConstraint& a, const cadcells::datastructures::PolyConstraint& b) {
    return features::sum_total_degree(proj, a) < features::sum_total_degree(proj, b);
}

inline bool min_tdeg(cadcells::datastructures::Projections& proj, const cadcells::datastructures::PolyConstraint& a, const cadcells::datastructures::PolyConstraint& b) {
    return proj.total_degree(a.lhs) < proj.total_degree(b.lhs); 
}

/**
 * Mnimimizing the number of non-linear constraints for techniques that use abstractions
 */

inline bool min_n_nonlin(cadcells::datastructures::Projections& proj, const Implicant& a, const Implicant& b) {
    std::size_t n_a = features::n_nonlin(proj, a);
    std::size_t n_b = features::n_nonlin(proj, b);
    if (n_a < n_b) return true;
    return (n_b == n_a) && sotd(proj, a, b);
}

/**
 * Mnimimizing the product of the total degree of all constraints
 */

inline bool min_prod_max_tdeg(cadcells::datastructures::Projections& proj, const Implicant& a, const Implicant& b) {
    std::size_t n_a = features::product_max_total_degree(proj, a);
    std::size_t n_b = features::product_max_total_degree(proj, b);
    if (n_a < n_b) return true;
    return (n_b == n_a) && sotd(proj, a, b);
}

} // namespace smtrat::covering_ng::formula::complexity
