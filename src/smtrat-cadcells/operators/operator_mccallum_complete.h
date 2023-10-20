#pragma once

#include "operator.h"


#include "../datastructures/roots.h"
#include "properties.h"
#include "rules.h"
#include "rules_null.h"

namespace smtrat::cadcells::operators {

template <>
struct PropertiesSet<op::mccallum_complete> {
    using type = datastructures::PropertiesT<properties::poly_sgn_inv,properties::poly_irreducible_sgn_inv,properties::poly_semi_sgn_inv,properties::poly_ord_inv,properties::poly_del,properties::cell_connected>;
};

template <>
inline bool project_basic_properties<op::mccallum_complete>(datastructures::SampledDerivation<PropertiesSet<op::mccallum_complete>::type>& deriv) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", &deriv);
    for(const auto& prop : deriv.properties<properties::poly_del>()) {
        if (!rules::poly_del(deriv, prop.poly)) return false;
    }
    for(const auto& prop : deriv.properties<properties::poly_ord_inv>()) {
        rules::poly_ord_inv_maybe_null(deriv, prop.poly);
    }
    for(const auto& prop : deriv.properties<properties::poly_semi_sgn_inv>()) {
        deriv.insert(properties::poly_sgn_inv{prop.poly});
    }
    for(const auto& prop : deriv.properties<properties::poly_sgn_inv>()) {
        rules::poly_sgn_inv(deriv, prop.poly, false);
    }
    return true;
}

template <>
inline void delineate_properties<op::mccallum_complete>(datastructures::SampledDerivation<PropertiesSet<op::mccallum_complete>::type>& deriv) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", &deriv);
    for(const auto& prop : deriv.properties<properties::poly_irreducible_sgn_inv>()) {
        rules::delineate(*deriv.delineated(), prop);
    }
}

template <>
inline bool project_cell_properties<op::mccallum_complete>(datastructures::CellRepresentation<PropertiesSet<op::mccallum_complete>::type>& repr) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", repr);
    auto& deriv = *repr.derivation;

    for (const auto poly : deriv.delin().nullified()) {
        if (deriv.contains(properties::poly_del{ poly })) {
            return false;
        }
    }

    for(const auto& poly : repr.description.polys()) {
        deriv.insert(properties::poly_del{ poly });
    }
    for(const auto& poly : repr.ordering.polys()) {
        deriv.insert(properties::poly_del{ poly });
    }

    if (deriv.contains(properties::cell_connected{deriv.level()})) {
        rules::cell_connected(deriv, repr.description, repr.ordering);
    }
    rules::cell_analytic_submanifold(deriv, repr.description);
    rules::cell_represents(deriv, repr.description);

    rules::root_ordering_holds(deriv.underlying().sampled(), repr.ordering);

    for(const auto& prop : deriv.properties<properties::poly_irreducible_sgn_inv>()) {
        if (repr.equational.find(prop.poly) != repr.equational.end()) {
            rules::poly_irreducible_sgn_inv_ec(deriv, repr.description, prop.poly);
        } else if (deriv.delin().nonzero().find(prop.poly) != deriv.delin().nonzero().end()) {
            rules::poly_irreducible_nonzero_sgn_inv(*deriv.delineated(), prop.poly);
        } else if (deriv.delin().nullified().find(prop.poly) != deriv.delin().nullified().end()) {
            rules::poly_irreducible_null_sgn_inv(deriv, prop.poly);
        } else {
            rules::poly_irreducible_sgn_inv(deriv, repr.description, repr.ordering, prop.poly);
        }
    }
    return true;
}



template <>
inline bool project_covering_properties<op::mccallum_complete>(datastructures::CoveringRepresentation<PropertiesSet<op::mccallum_complete>::type>& repr) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", repr);
    for (auto& cell_repr : repr.cells) {
        if (!project_cell_properties<op::mccallum_complete>(cell_repr)) {
            return false;
        }
    }
    auto cov = repr.get_covering();
    rules::root_ordering_holds(repr.cells.front().derivation->underlying().sampled(), repr.ordering);
    rules::covering_holds(repr.cells.front().derivation->underlying().delineated(), cov, repr.ordering);
    return true;
}

}
