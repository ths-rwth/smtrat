#pragma once

#include <vector>

namespace smtrat::cadcells::algorithms {

/**
 * Computes a delineation w.r.t. a set of constraints.
 * 
 * A set of polynomials that are univariate under a sample induces a delineation (i.e. the order of their roots, polynomials without roots and nullified polynomials). This delineation is generalized such that the ordering on the roots etc is invariant.
 * 
 * @param constraints Atoms of the same level.
 * @param sample A sample such that all but the highest variable in @ref constraints are assigned.
 * @return A sampled derivation which contains the information to keep the delineation invariant. 
 */
template <cadcells::operators::op op, representation::DelineationHeuristic delineation_heuristic>
std::optional<datastructures::SampledDerivationRef<typename operators::PropertiesSet<op>::type>> get_delineation(datastructures::Projections& proj, const FormulasT& cs, const Assignment& sample) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.algorithms.onecell", cs << ", " << sample);

    auto vars = proj.polys().var_order();
    auto tmp_sample = sample;

    auto deriv = datastructures::make_derivation<typename operators::PropertiesSet<op>::type>(proj, sample, sample.size() + 1).delineated_ref();

    for (const auto& c: cs) {
        SMTRAT_LOG_FUNC("smtrat.cadcells.algorithms.onecell", c << ", " << sample);
        Poly p;
        if (c.type() == carl::FormulaType::CONSTRAINT) {
            p = c.constraint().lhs();
        } else if (c.type() == carl::FormulaType::VARCOMPARE) {
            p = c.variable_comparison().defining_polynomial();
        } else {
            assert(false);
            return std::nullopt;
        }
        assert(cadcells::helper::level_of(vars, p) == sample.size()+1);
        deriv->insert(operators::properties::poly_sgn_inv{ proj.polys()(p) });
        // TODO can we use equational constraints?     
    }
    operators::project_basic_properties<op>(*deriv);
    operators::delineate_properties<op>(*deriv);

    SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Computing delineation representation");
    auto delineation_repr = representation::delineation<delineation_heuristic>::compute(deriv);
    if (!delineation_repr) {
        return std::nullopt;
    }
    SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got representation " << *delineation_repr);

    SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Compute delineation projection");
    operators::project_delineation_properties<op>(*delineation_repr);
    
    return deriv->underlying().sampled_ref();
}

}