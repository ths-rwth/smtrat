#pragma once

namespace smtrat::covering_ng::formula::node_ds::complexity {
    
inline bool min_tdeg_ordering(const Node& a, const Node& b) {
    return a.c().max_total_degree < b.c().max_total_degree;
}

inline bool min_lvl_min_tdeg_ordering(const Node& a, const Node& b) {
    return a.c().max_level < b.c().max_level || (a.c().max_level == b.c().max_level && a.c().max_total_degree < b.c().max_total_degree);
}

inline bool min_tdeg_min_size_implicant(const boost::container::flat_set<cadcells::Constraint>& a, const boost::container::flat_set<cadcells::Constraint>& b) {
    // TODO this is rather inefficient
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

inline bool min_size_min_tdeg_implicant(const boost::container::flat_set<cadcells::Constraint>& a, const boost::container::flat_set<cadcells::Constraint>& b) {
    // TODO this is rather inefficient
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


// TODO orderings

} // namespace smtrat::covering_ng::formula::complexity
