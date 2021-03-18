#pragma once

#include "../datastructures/roots.h"
#include "../datastructures/polynomials.h"

namespace smtrat::cadcells::algorithms::helper {

inline MultivariateRootT as_multivariate_root(const datastructures::PolyPool& pool, carl::Variable main_var, datastructures::IndexedRoot r) {
    const Poly& poly = pool(r.poly);
    assert(carl::variables(poly).has(main_var));
    return MultivariateRootT(Poly(carl::UnivariatePolynomial<Poly>(MultivariateRootT::var(), carl::to_univariate_polynomial(poly, main_var).coefficients())), r.index);
}

FormulaT to_formula(const datastructures::PolyPool& pool, carl::Variable main_var, datastructures::CellDescription& c) {
    if (c.is_section()) {
        return FormulaT(VariableComparisonT(main_var, as_multivariate_root(pool,main_var,c.section_defining()), carl::Relation::EQ));
    } else {
        FormulasT subformulas;
        if (c.lower()) {
            subformulas.emplace_back(VariableComparisonT(main_var, as_multivariate_root(pool,main_var,*c.lower()), carl::Relation::GREATER));
        }
        FormulaT lower(carl::FormulaType::TRUE);
        if (c.upper()) {
            subformulas.emplace_back(VariableComparisonT(main_var, as_multivariate_root(pool,main_var,*c.upper()), carl::Relation::LESS));
        }
        return FormulaT(carl::FormulaType::AND, std::move(subformulas));
    } 
}

}