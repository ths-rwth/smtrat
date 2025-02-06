#pragma once

#include "properties.h"
#include "properties_util.h"
#include "../datastructures/derivation.h"

namespace smtrat::cadcells::operators::rules {

template<typename P>
bool poly_constr_truth_inv(datastructures::SampledDerivation<P>& deriv, datastructures::PolyConstraint constr) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "truth_inv(" << constr << ")");

    auto truth = deriv.proj().evaluate(deriv.sample(),constr);
    if (!boost::indeterminate(truth)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "truth_inv(" << constr << ") is not derivable as " << constr << " has no truth value at " << deriv.sample());
        return false;
    }

    if ((carl::is_strict(constr.relation) && truth == false) || (!carl::is_strict(constr.relation) && truth == true)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "truth_inv(" << constr << ") <= semi_sgn_inv(" << constr.lhs << ")");
        deriv.insert(operators::properties::poly_semi_sgn_inv{ constr.lhs });
    } else {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "truth_inv(" << constr << ") <= sgn_inv(" << constr.lhs << ")");
        deriv.insert(operators::properties::poly_sgn_inv{ constr.lhs });
    }
    return true;
}

template<typename P>
void delineate(datastructures::SampledDerivation<P>& deriv, const properties::iroot_constraint_truth_inv& prop, bool filter = false) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "delineate(" << prop << ")");
    SMTRAT_STATISTICS_CALL(statistics().rules_delineate_sgn_inv_called(prop.constr.bound.poly));

    if (deriv.proj().num_roots(deriv.sample(), prop.constr.bound.poly) < prop.constr.bound.index) {
        assert(false);
        return;
    }

    auto truth = deriv.proj().evaluate(deriv.sample(), prop.constr);
    if (!truth) {
        assert(false);
        return;
    }

    deriv.delin().add_root(deriv.proj().evaluate(deriv.sample(), prop.constr.bound), datastructures::TaggedIndexedRoot{prop.constr.bound, filter && carl::is_strict(prop.constr.relation)});
}

template<typename P>
bool iroot_constr_truth_inv(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& /*cell*/, const datastructures::IndexedRootOrdering& /*ordering*/, datastructures::IndexedRootConstraint constr) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "truth_inv(" << constr << ")");

    if (deriv.proj().num_roots(deriv.sample(), constr.bound.poly) < constr.bound.index) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "truth_inv(" << constr << ") is not derivable as " << constr.bound << " is not defined at " << deriv.sample());
        return false;
    }

    auto truth = deriv.proj().evaluate(deriv.sample(),constr);
    if (!truth) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "truth_inv(" << constr << ") is not derivable as " << constr << " is is not true at " << deriv.sample());
        return false;
    }

    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "truth_inv(" << constr << ") <= some properties");
    assert(deriv.contains(operators::properties::poly_del{ constr.bound.poly }));

    return true;
}

}