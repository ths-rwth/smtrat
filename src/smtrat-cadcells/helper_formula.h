#pragma once

#include "common.h"
#include "datastructures/roots.h"
#include "datastructures/polynomials.h"

namespace smtrat::cadcells::helper {

/**
 * Converts an @ref datastructures::IndexedRoot to a @ref MultivariateRoot.
 */
inline MultivariateRoot as_multivariate_root(const datastructures::PolyPool& pool, carl::Variable main_var, datastructures::IndexedRoot r) {
    const Polynomial& poly = pool(r.poly);
    assert(carl::variables(poly).has(main_var));
    return MultivariateRoot(poly, r.index, main_var);
}

/**
 * Converts a @ref datastructures::SymbolicInterval to a @ref CNF.
 */
inline CNF to_formula(const datastructures::PolyPool& pool, carl::Variable main_var, const datastructures::SymbolicInterval& c) {
    CNF cnf;
    if (c.is_section()) {
        cnf.emplace_back();
        cnf.back().emplace_back(VariableComparison(main_var, as_multivariate_root(pool,main_var,c.section_defining()), carl::Relation::EQ));
    } else {
        if (!c.lower().is_infty()) {
            auto rel = c.lower().is_strict() ? carl::Relation::GREATER : carl::Relation::GEQ;
            if (c.lower().value().is_root()) {
                cnf.emplace_back();
                cnf.back().emplace_back(VariableComparison(main_var, as_multivariate_root(pool,main_var,c.lower().value().root()), rel));
            } else {
                assert(c.lower().value().is_cmaxmin());
                for (const auto& rs : c.lower().value().cmaxmin().roots) {
                    cnf.emplace_back();
                    for (const auto& r : rs) {
                        cnf.back().emplace_back(VariableComparison(main_var, as_multivariate_root(pool,main_var,r), rel));
                    }
                }
            }
        }
        if (!c.upper().is_infty()) {
            auto rel = c.upper().is_strict() ? carl::Relation::LESS : carl::Relation::LEQ;
            if (c.upper().value().is_root()) {
                cnf.emplace_back();
                cnf.back().emplace_back(VariableComparison(main_var, as_multivariate_root(pool,main_var,c.upper().value().root()), rel));
            } else {
                assert(c.upper().value().is_cminmax());
                for (const auto& rs : c.upper().value().cminmax().roots) {
                    cnf.emplace_back();
                    for (const auto& r : rs) {
                        cnf.back().emplace_back(VariableComparison(main_var, as_multivariate_root(pool,main_var,r), rel));
                    }
                }
            }
        }
    } 
    return cnf;
}

}