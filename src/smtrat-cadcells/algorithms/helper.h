#pragma once

namespace smtrat::cadcells::algorithms::helper {

inline MultivariateRootT as_multivariate_root(const poly_pool& pool, carl::Variable main_var, indexed_root r) {
    const Poly& poly = pool(r.poly);
    assert(poly.gatherVariables().count(main_var) == 1);
    return MultivariateRootT(Poly(carl::UnivariatePolynomial<Poly>(MultivariateRootT::var(), carl::to_univariate_polynomial(poly, main_var).coefficients())), r.idx);
}

FormulaT to_formula(const poly_pool& pool, carl::Variable main_var, cell c) {
    if (c.is_section()) {
        return FormulaT(VarComparisonT(main_var, as_multivariate_root(pool,main_var,c.sector_defining()), carl::Relation::EQ));
    } else {
        FormulasT subformulas;
        if (c.lower()) {
            subformulas.emplace_back(VarComparisonT(main_var, as_multivariate_root(pool,main_var,*c.lower()), carl::Relation::GEQ));
        }
        FormulaT lower(carl::FormulaType::TRUE);
        if (c.upper()) {
            subformulas.emplace_back(VarComparisonT(main_var, as_multivariate_root(pool,main_var,*c.upper()), carl::Relation::LEQ));
        }
        return FormulaT(carl::FormulaType::AND, std::move(subformulas));
    } 
}

}