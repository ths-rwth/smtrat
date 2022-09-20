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
 * Converts a @ref datastructures::SymbolicInterval to an @ref Atom.
 */
std::vector<Atom> to_formula(const datastructures::PolyPool& pool, carl::Variable main_var, const datastructures::SymbolicInterval& c) {
    std::vector<Atom> atoms;
    if (c.is_section()) {
        atoms.emplace_back(VariableComparison(main_var, as_multivariate_root(pool,main_var,c.section_defining()), carl::Relation::EQ));
    } else {
        if (!c.lower().is_infty()) {
            auto rel = c.lower().is_strict() ? carl::Relation::GREATER : carl::Relation::GEQ;
            if (c.lower().value().is_root()) {
                atoms.emplace_back(VariableComparison(main_var, as_multivariate_root(pool,main_var,c.lower().value().root()), rel));
            } else {
                assert(c.lower().value().is_cmax());
                for (const auto& r : c.lower().value().cmax().roots) {
                    atoms.emplace_back(VariableComparison(main_var, as_multivariate_root(pool,main_var,r), rel));
                }
            }
        }
        if (!c.upper().is_infty()) {
            auto rel = c.upper().is_strict() ? carl::Relation::LESS : carl::Relation::LEQ;
            if (c.upper().value().is_root()) {
                atoms.emplace_back(VariableComparison(main_var, as_multivariate_root(pool,main_var,c.upper().value().root()), rel));
            } else {
                assert(c.upper().value().is_cmin());
                for (const auto& r : c.upper().value().cmin().roots) {
                    atoms.emplace_back(VariableComparison(main_var, as_multivariate_root(pool,main_var,r), rel));
                }
            }
        }
    } 
    return atoms;
}

}