#pragma once

namespace smtrat::covering_ng::formula::complexity {
    
// TODO sum of total degrees (see Dolzmann et al 2004) (sum of tdegs of all monomials)

inline bool min_max_tdeg_min_size_fact(cadcells::datastructures::Projections& proj, const boost::container::flat_set<cadcells::Constraint>& a, const boost::container::flat_set<cadcells::Constraint>& b) {
    std::size_t a_max_total_degree = 0;
    for (const auto& el : a) {
        for (const auto f : proj.factors_nonconst(proj.polys()(el.lhs()))) {
            a_max_total_degree = std::max(a_max_total_degree, proj.total_degree(f));
        }
    }
    std::size_t b_max_total_degree = 0;
    for (const auto& el : b) {
        for (const auto f : proj.factors_nonconst(proj.polys()(el.lhs()))) {
            b_max_total_degree = std::max(b_max_total_degree, proj.total_degree(f));
        }
    }
    return a_max_total_degree < b_max_total_degree || (a_max_total_degree == b_max_total_degree && a.size() < b.size());
}

inline bool min_max_tdeg_min_size(const boost::container::flat_set<cadcells::Constraint>& a, const boost::container::flat_set<cadcells::Constraint>& b) {
    std::size_t a_max_total_degree = 0;
    for (const auto& el : a) {
        a_max_total_degree = std::max(a_max_total_degree, el.lhs().total_degree());
    }
    std::size_t b_max_total_degree = 0;
    for (const auto& el : b) {
        b_max_total_degree = std::max(b_max_total_degree, el.lhs().total_degree());
    }
    return a_max_total_degree < b_max_total_degree || (a_max_total_degree == b_max_total_degree && a.size() < b.size());
}

inline bool min_size_min_tdeg(const boost::container::flat_set<cadcells::Constraint>& a, const boost::container::flat_set<cadcells::Constraint>& b) {
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
        std::size_t a_max_total_degree = 0;
        for (const auto& el : a) {
            a_max_total_degree = std::max(a_max_total_degree, el.lhs().total_degree());
        }
        std::size_t b_max_total_degree = 0;
        for (const auto& el : b) {
            b_max_total_degree = std::max(b_max_total_degree, el.lhs().total_degree());
        }
        return a_max_total_degree < b_max_total_degree ;
    }
}

inline bool min_tdeg(const cadcells::Constraint& a, const cadcells::Constraint& b) {
    assert(a.lhs().main_var() == b.lhs().main_var());
    return a.lhs().total_degree() < b.lhs().total_degree(); 
}



} // namespace smtrat::covering_ng::formula::complexity
