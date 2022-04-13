#pragma once

#include "../datastructures/roots.h"
#include "../datastructures/polynomials.h"

namespace smtrat::cadcells::algorithms::helper {

/**
 * Converts an @ref datastructures::IndexedRoot to a @ref MultivariateRootT.
 */
inline MultivariateRootT as_multivariate_root(const datastructures::PolyPool& pool, carl::Variable main_var, datastructures::IndexedRoot r) {
    const Poly& poly = pool(r.poly);
    assert(carl::variables(poly).has(main_var));
    return MultivariateRootT(Poly(carl::UnivariatePolynomial<Poly>(MultivariateRootT::var(), carl::to_univariate_polynomial(poly, main_var).coefficients())), r.index);
}

/**
 * Converts a @ref datastructures::SymbolicInterval to a @ref FormulaT.
 */
FormulaT to_formula(const datastructures::PolyPool& pool, carl::Variable main_var, datastructures::SymbolicInterval& c) {
    if (c.is_section()) {
        return FormulaT(VariableComparisonT(main_var, as_multivariate_root(pool,main_var,c.section_defining()), carl::Relation::EQ));
    } else {
        FormulasT subformulas;
        if (c.lower().is_strict()) {
            subformulas.emplace_back(VariableComparisonT(main_var, as_multivariate_root(pool,main_var,c.lower().value()), carl::Relation::GREATER));
        } else if (c.lower().is_weak()) {
            subformulas.emplace_back(VariableComparisonT(main_var, as_multivariate_root(pool,main_var,c.lower().value()), carl::Relation::GEQ));
        }
        FormulaT lower(carl::FormulaType::TRUE);
        if (c.upper().is_strict()) {
            subformulas.emplace_back(VariableComparisonT(main_var, as_multivariate_root(pool,main_var,c.upper().value()), carl::Relation::LESS));
        } else if (c.upper().is_weak()) {
            subformulas.emplace_back(VariableComparisonT(main_var, as_multivariate_root(pool,main_var,c.upper().value()), carl::Relation::LEQ));
        }
        return FormulaT(carl::FormulaType::AND, std::move(subformulas));
    } 
}

}