#pragma once

namespace smtrat::covering_ng::formula::complexity {
    
inline bool min_tdeg_ordering(const FormulaEvaluation& a, const FormulaEvaluation& b) {
    // return true;
    //return a.c().max_level < b.c().max_level || (a.c().max_level == b.c().max_level && a.c().max_total_degree < b.c().max_total_degree);
    return a.c().max_total_degree < b.c().max_total_degree;
}

inline bool min_lvl_min_tdeg_ordering(const FormulaEvaluation& a, const FormulaEvaluation& b) {
    return a.c().max_level < b.c().max_level || (a.c().max_level == b.c().max_level && a.c().max_total_degree < b.c().max_total_degree);
}

// TODO orderings

} // namespace smtrat::covering_ng::formula::complexity
