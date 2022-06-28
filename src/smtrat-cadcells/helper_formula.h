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
        if (c.lower().is_strict()) {
            atoms.emplace_back(VariableComparison(main_var, as_multivariate_root(pool,main_var,c.lower().value()), carl::Relation::GREATER));
        } else if (c.lower().is_weak()) {
            atoms.emplace_back(VariableComparison(main_var, as_multivariate_root(pool,main_var,c.lower().value()), carl::Relation::GEQ));
        }
        if (c.upper().is_strict()) {
            atoms.emplace_back(VariableComparison(main_var, as_multivariate_root(pool,main_var,c.upper().value()), carl::Relation::LESS));
        } else if (c.upper().is_weak()) {
            atoms.emplace_back(VariableComparison(main_var, as_multivariate_root(pool,main_var,c.upper().value()), carl::Relation::LEQ));
        }
    } 
    return atoms;
}

}