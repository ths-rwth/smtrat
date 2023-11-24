#pragma once

namespace smtrat::covering_ng::formula::complexity {


namespace features {

auto size_fact(cadcells::datastructures::Projections& proj, const boost::container::flat_set<cadcells::Constraint>& a) {
    std::size_t a_size = 0;
    for (const auto& el : a) {
        a_size += proj.factors_nonconst(proj.polys()(el.lhs())).size();
    }
    return a_size;
}

auto max_total_degree(cadcells::datastructures::Projections& proj, const boost::container::flat_set<cadcells::Constraint>& a) {
    std::size_t a_max_total_degree = 0;
    for (const auto& el : a) {
        a_max_total_degree = std::max(a_max_total_degree, proj.total_degree(proj.polys()(el.lhs())));
    }
    return a_max_total_degree;
}

auto max_total_degree_fact(cadcells::datastructures::Projections& proj, const boost::container::flat_set<cadcells::Constraint>& a) {
    std::size_t a_max_total_degree = 0;
    for (const auto& el : a) {
        for (const auto f : proj.factors_nonconst(proj.polys()(el.lhs()))) {
            a_max_total_degree = std::max(a_max_total_degree, proj.total_degree(f));
        }
    }
    return a_max_total_degree;
}

auto sum_max_degree(cadcells::datastructures::Projections& proj, const boost::container::flat_set<cadcells::Constraint>& a) {
    std::size_t result = 0;
    for (const auto& el : a) {
        result += proj.degree(proj.polys()(el.lhs()));
    }
    return result;
}

auto sum_max_degree_fact(cadcells::datastructures::Projections& proj, const boost::container::flat_set<cadcells::Constraint>& a) {
    std::size_t result = 0;
    for (const auto& el : a) {
        for (const auto f : proj.factors_nonconst(proj.polys()(el.lhs()))) {
            result += proj.degree(f);
        }
    }
    return result;
}

auto avg_avg_degree(cadcells::datastructures::Projections& proj, const boost::container::flat_set<cadcells::Constraint>& a) {
    std::size_t sum = 0;
    std::size_t count = 0;
    for (const auto& el : a) {
        for (auto d : proj.monomial_degrees(proj.polys()(el.lhs()))) {
            sum += d;
            count++;
        }
    }
    return static_cast<double>(sum)/static_cast<double>(count);
}

auto avg_avg_degree_fact(cadcells::datastructures::Projections& proj, const boost::container::flat_set<cadcells::Constraint>& a) {
    std::size_t sum = 0;
    std::size_t count = 0;
    for (const auto& el : a) {
        for (const auto f : proj.factors_nonconst(proj.polys()(el.lhs()))) {
            for (auto d : proj.monomial_degrees(f)) {
                sum += d;
                count++;
            }
        }
    }
    return static_cast<double>(sum)/static_cast<double>(count);
}

auto sum_sum_degree(cadcells::datastructures::Projections& proj, const boost::container::flat_set<cadcells::Constraint>& a) {
    std::size_t sum = 0;
    for (const auto& el : a) {
        for (auto d : proj.monomial_degrees(proj.polys()(el.lhs()))) {
            sum += d;
        }
    }
    return sum;
}

auto sum_sum_degree_fact(cadcells::datastructures::Projections& proj, const boost::container::flat_set<cadcells::Constraint>& a) {
    std::size_t sum = 0;
    for (const auto& el : a) {
        for (const auto f : proj.factors_nonconst(proj.polys()(el.lhs()))) {
            for (auto d : proj.monomial_degrees(f)) {
                sum += d;
            }
        }
    }
    return sum;
}

auto sum_sum_total_degree(cadcells::datastructures::Projections& proj, const boost::container::flat_set<cadcells::Constraint>& a) {
    std::size_t sum = 0;
    for (const auto& el : a) {
        for (auto d : proj.monomial_total_degrees(proj.polys()(el.lhs()))) {
            sum += d;
        }
    }
    return sum;
}

auto sum_sum_total_degree_fact(cadcells::datastructures::Projections& proj, const boost::container::flat_set<cadcells::Constraint>& a) {
    std::size_t sum = 0;
    for (const auto& el : a) {
        for (const auto f : proj.factors_nonconst(proj.polys()(el.lhs()))) {
            for (auto d : proj.monomial_total_degrees(f)) {
                sum += d;
            }
        }
    }
    return sum;
}

}

/**
 * Inspired by Pickering, Lynn, Tereso Del Rio Almajano, Matthew England, and Kelly Cohen. ‘Explainable AI Insights for Symbolic Computation: A Case Study on Selecting the Variable Ordering for Cylindrical Algebraic Decomposition’. arXiv, 29 August 2023. http://arxiv.org/abs/2304.12154.
 */
inline bool pickering(cadcells::datastructures::Projections& proj, const boost::container::flat_set<cadcells::Constraint>& a, const boost::container::flat_set<cadcells::Constraint>& b) {
    auto a_sum_max_degree = features::sum_max_degree(proj, a);
    auto b_sum_max_degree = features::sum_max_degree(proj, b);
    if (a_sum_max_degree != b_sum_max_degree) return a_sum_max_degree < b_sum_max_degree;
    else {
        auto a_avg_avg_degree = features::avg_avg_degree(proj, a);
        auto b_avg_avg_degree = features::avg_avg_degree(proj, b);
        if (a_avg_avg_degree != b_avg_avg_degree) return a_avg_avg_degree < b_avg_avg_degree;
        else {
            auto a_sum_sum_degree = features::sum_sum_degree(proj, a);
            auto b_sum_sum_degree = features::sum_sum_degree(proj, b);
            return a_sum_sum_degree < b_sum_sum_degree;
        }
    }
}

inline bool pickering_fact(cadcells::datastructures::Projections& proj, const boost::container::flat_set<cadcells::Constraint>& a, const boost::container::flat_set<cadcells::Constraint>& b) {
    auto a_sum_max_degree = features::sum_max_degree_fact(proj, a);
    auto b_sum_max_degree = features::sum_max_degree_fact(proj, b);
    if (a_sum_max_degree != b_sum_max_degree) return a_sum_max_degree < b_sum_max_degree;
    else {
        auto a_avg_avg_degree = features::avg_avg_degree_fact(proj, a);
        auto b_avg_avg_degree = features::avg_avg_degree_fact(proj, b);
        if (a_avg_avg_degree != b_avg_avg_degree) return a_avg_avg_degree < b_avg_avg_degree;
        else {
            auto a_sum_sum_degree = features::sum_sum_degree_fact(proj, a);
            auto b_sum_sum_degree = features::sum_sum_degree_fact(proj, b);
            return a_sum_sum_degree < b_sum_sum_degree;
        }
    }
}

/**
 * Dolzmann et al 2004
 */
inline bool sotd(cadcells::datastructures::Projections& proj, const boost::container::flat_set<cadcells::Constraint>& a, const boost::container::flat_set<cadcells::Constraint>& b) {
    auto a_sum_sum_total_degree = features::sum_sum_total_degree(proj, a);
    auto b_sum_sum_total_degree = features::sum_sum_total_degree(proj, b);
    return a_sum_sum_total_degree < b_sum_sum_total_degree || (a_sum_sum_total_degree == b_sum_sum_total_degree && a.size() < b.size());
}

inline bool sotd_fact(cadcells::datastructures::Projections& proj, const boost::container::flat_set<cadcells::Constraint>& a, const boost::container::flat_set<cadcells::Constraint>& b) {
    auto a_sum_sum_total_degree = features::sum_sum_total_degree_fact(proj, a);
    auto b_sum_sum_total_degree = features::sum_sum_total_degree_fact(proj, b);
    auto a_size = features::size_fact(proj, a);
    auto b_size = features::size_fact(proj, b);
    return a_sum_sum_total_degree < b_sum_sum_total_degree || (a_sum_sum_total_degree == b_sum_sum_total_degree && a_size < b_size);
}


inline bool min_max_tdeg_min_size_fact(cadcells::datastructures::Projections& proj, const boost::container::flat_set<cadcells::Constraint>& a, const boost::container::flat_set<cadcells::Constraint>& b) {
    auto a_max_total_degree = features::max_total_degree_fact(proj, a);
    auto b_max_total_degree = features::max_total_degree_fact(proj, b);
    auto a_size = features::size_fact(proj, a);
    auto b_size = features::size_fact(proj, b);
    return a_max_total_degree < b_max_total_degree || (a_max_total_degree == b_max_total_degree && a_size < b_size);
}

inline bool min_max_tdeg_min_size(cadcells::datastructures::Projections& proj, const boost::container::flat_set<cadcells::Constraint>& a, const boost::container::flat_set<cadcells::Constraint>& b) {
    auto a_max_total_degree = features::max_total_degree(proj, a);
    auto b_max_total_degree = features::max_total_degree(proj, b);
    return a_max_total_degree < b_max_total_degree || (a_max_total_degree == b_max_total_degree && a.size() < b.size());
}

inline bool min_size_min_tdeg(cadcells::datastructures::Projections& proj, const boost::container::flat_set<cadcells::Constraint>& a, const boost::container::flat_set<cadcells::Constraint>& b) {
    std::vector<std::size_t> a_levels;
    for (const auto& el : a) a_levels.push_back(carl::level_of(el.lhs()));
    std::vector<std::size_t> b_levels;
    for (const auto& el : b) b_levels.push_back(carl::level_of(el.lhs()));
    auto level = *std::max_element(a_levels.begin(), a_levels.end());
    assert(level == *std::max_element(b_levels.begin(), b_levels.end()));

    auto a_ml_size = std::count(a_levels.begin(), a_levels.end(), level);
    auto b_ml_size = std::count(b_levels.begin(), b_levels.end(), level);

    if (a_ml_size < b_ml_size) return true;
    else if (a_ml_size > b_ml_size) return false;
    else if (a.size() < b.size()) return true;
    else if (a.size() > b.size()) return false;
    else {
        auto a_max_total_degree = features::max_total_degree(proj, a);
        auto b_max_total_degree = features::max_total_degree(proj, b);
        return a_max_total_degree < b_max_total_degree ;
    }
}

inline bool min_tdeg(const cadcells::Constraint& a, const cadcells::Constraint& b) {
    assert(a.lhs().main_var() == b.lhs().main_var());
    return a.lhs().total_degree() < b.lhs().total_degree(); 
}



} // namespace smtrat::covering_ng::formula::complexity
