#pragma once

namespace smtrat::covering_ng::formula::complexity {
    
inline bool min_tdeg_ordering(const FormulaEvaluation& a, const FormulaEvaluation& b) {
    return a.c().max_total_degree < b.c().max_total_degree;
}

inline bool min_lvl_min_tdeg_ordering(const FormulaEvaluation& a, const FormulaEvaluation& b) {
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


// TODO orderings

} // namespace smtrat::covering_ng::formula::complexity
