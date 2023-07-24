#pragma once

#include "operator.h"


#include "../datastructures/roots.h"
#include "properties.h"
#include "rules.h"

namespace smtrat::cadcells::operators {

template <>
struct PropertiesSet<op::mccallum> {
    using type = datastructures::PropertiesT<properties::poly_sgn_inv,properties::poly_irreducible_sgn_inv,properties::poly_semi_sgn_inv,properties::poly_ord_inv,properties::poly_del,properties::cell_connected>;
};

template <>
inline bool project_basic_properties<op::mccallum>(datastructures::DelineatedDerivation<PropertiesSet<op::mccallum>::type>& deriv) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", &deriv);
    for(const auto& prop : deriv.properties<properties::poly_semi_sgn_inv>()) {
        deriv.insert(properties::poly_sgn_inv{prop.poly});
    }
    for(const auto& prop : deriv.properties<properties::poly_sgn_inv>()) {
        rules::poly_sgn_inv(deriv, prop.poly);
    }
    return true;
}

template <>
inline void delineate_properties<op::mccallum>(datastructures::DelineatedDerivation<PropertiesSet<op::mccallum>::type>& deriv) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", &deriv);
    for(const auto& prop : deriv.properties<properties::poly_irreducible_sgn_inv>()) {
        rules::delineate(deriv, prop);
    }
}

template <>
inline void delineate_properties<op::mccallum>(datastructures::SampledDerivation<PropertiesSet<op::mccallum>::type>& deriv) {
    delineate_properties<op::mccallum>(*deriv.delineated());
}

template <>
inline bool project_delineated_cell_properties<op::mccallum>(datastructures::CellRepresentation<PropertiesSet<op::mccallum>::type>& repr) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", repr);
    auto& deriv = *repr.derivation;

    for(const auto& poly : repr.description.polys()) {
        deriv.insert(properties::poly_del{ poly });
    }
    for(const auto& poly : repr.ordering.polys()) {
        deriv.insert(properties::poly_del{ poly });
    }

    for (const auto& poly : deriv.delin().nonzero()) {
        if (repr.equational.find(poly) == repr.equational.end()) {
            rules::poly_irreducible_nonzero_sgn_inv(*deriv.delineated(), poly);
        }
    }

    if (deriv.contains(properties::cell_connected{deriv.level()})) {
        rules::cell_connected(deriv, repr.description, repr.ordering);
    }
    rules::cell_analytic_submanifold(deriv, repr.description);
    rules::cell_represents(deriv, repr.description);

    for (const auto& poly : repr.equational) {
        rules::poly_irreducible_sgn_inv_ec(deriv, repr.description, poly);
    }

    rules::root_ordering_holds(deriv.underlying().sampled(), repr.ordering);

    for(const auto& prop : deriv.properties<properties::poly_irreducible_sgn_inv>()) {
        if (repr.equational.find(prop.poly) == repr.equational.end() && deriv.delin().nonzero().find(prop.poly) == deriv.delin().nonzero().end()) {
            rules::poly_irreducible_sgn_inv(deriv, repr.description, repr.ordering, prop.poly);
        }
    }
    return true;
}

template <>
inline bool project_cell_properties<op::mccallum>(datastructures::SampledDerivation<PropertiesSet<op::mccallum>::type>& deriv) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", &deriv);
    for(const auto& prop : deriv.properties<properties::poly_del>()) {
        if (!rules::poly_del(deriv, prop.poly)) return false;
    }
    for(const auto& prop : deriv.properties<properties::poly_ord_inv>()) {
        rules::poly_ord_inv(deriv, prop.poly);
    }
    return true;
}

template <>
inline bool project_covering_properties<op::mccallum>(datastructures::CoveringRepresentation<PropertiesSet<op::mccallum>::type>& repr) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", repr);
    for (auto& cell_repr : repr.cells) {
        project_delineated_cell_properties<op::mccallum>(cell_repr);
    }
    auto cov = repr.get_covering();
    rules::root_ordering_holds(repr.cells.front().derivation->underlying().sampled(), repr.ordering);
    rules::covering_holds(repr.cells.front().derivation->underlying().delineated(), cov, repr.ordering);
    return true;
}

}
