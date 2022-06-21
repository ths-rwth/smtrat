#pragma once

#include "operator.h"


#include "../datastructures/roots.h"
#include "properties.h"
#include "rules.h"
#include "delineation.h"


namespace smtrat::cadcells::operators {

template <>
struct PropertiesSet<op::mccallum_filtered> {
    using type = datastructures::PropertiesT<properties::poly_sgn_inv,properties::poly_irreducible_sgn_inv,properties::poly_ord_inv,properties::root_well_def,properties::poly_pdel,properties::cell_connected,properties::root_inv>;
};

template <>
inline bool project_basic_properties<op::mccallum_filtered>(datastructures::DelineatedDerivation<PropertiesSet<op::mccallum_filtered>::type>& deriv) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", &deriv);
    for(const auto& prop : deriv.properties<properties::poly_sgn_inv>()) {
        rules::poly_sgn_inv(deriv, prop.poly);
    }
    return true;
}

template <>
inline void delineate_properties<op::mccallum_filtered>(datastructures::DelineatedDerivation<PropertiesSet<op::mccallum_filtered>::type>& deriv) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", &deriv);
    for(const auto& prop : deriv.properties<properties::poly_irreducible_sgn_inv>()) {
        delineation::delineate(deriv, prop);
    }
     for(const auto& prop : deriv.properties<properties::root_inv>()) {
        delineation::delineate(deriv, prop);
    }
}

template <>
inline bool project_delineated_cell_properties<op::mccallum_filtered>(datastructures::CellRepresentation<PropertiesSet<op::mccallum_filtered>::type>& repr, bool cell_represents) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", repr << ", " << cell_represents);
    auto& deriv = *repr.derivation;

    // for(const auto& prop : deriv.properties<properties::poly_irreducible_sgn_inv>()) {
    //     if (repr.equational.find(prop.poly) == repr.equational.end()) {
    //         deriv.insert(properties::poly_pdel{ prop.poly });
    //     }
    // }
    for(const auto& poly : repr.description.polys()) {
        deriv.insert(properties::poly_pdel{ poly });
    }
    for(const auto& poly : repr.ordering.polys()) {
        deriv.insert(properties::poly_pdel{ poly });
    }

    for (const auto& poly : deriv.delin().nonzero()) {
        if (repr.equational.find(poly) == repr.equational.end()) {
            rules::poly_irrecubile_nonzero_sgn_inv(*deriv.delineated(), poly);
        }
    }

    if (deriv.contains(properties::cell_connected{deriv.level()})) {
        rules::cell_connected(deriv, repr.description, repr.ordering);
    }
    rules::cell_analytic_submanifold(deriv, repr.description);
    if (cell_represents) {
        rules::cell_represents(deriv, repr.description);
    } else {
        rules::cell_well_def(deriv, repr.description);
    }

    if (!repr.equational.empty()) {
        deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(repr.description.section_defining().poly) });
    }
    for (const auto& poly : repr.equational) {
        rules::poly_irreducible_sgn_inv_ec(deriv, repr.description, poly);
    }

    if (!rules::root_ordering_holds_filtered(deriv.underlying().sampled(), repr.ordering)) return false;

    for(const auto& prop : deriv.properties<properties::poly_irreducible_sgn_inv>()) {
        if (repr.equational.find(prop.poly) == repr.equational.end() && deriv.delin().nonzero().find(prop.poly) == deriv.delin().nonzero().end()) {
            if (!rules::poly_irreducible_sgn_inv_filtered(deriv, repr.description, repr.ordering, prop.poly)) return false;
        }
    }
    for(const auto& prop : deriv.properties<properties::root_inv>()) {
        if (repr.equational.find(prop.root.poly) == repr.equational.end()) {
            rules::root_inv(deriv, repr.description, repr.ordering, prop.root);
        }
    }
    return true;
}

template <>
inline bool project_cell_properties<op::mccallum_filtered>(datastructures::SampledDerivation<PropertiesSet<op::mccallum_filtered>::type>& deriv) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", &deriv);
    for(const auto& prop : deriv.properties<properties::root_well_def>()) {
        rules::root_well_def(deriv, prop.root);
    }
    for(const auto& prop : deriv.properties<properties::poly_pdel>()) {
        if (!rules::poly_pdel(deriv, prop.poly)) return false;
    }
    for(const auto& prop : deriv.properties<properties::poly_ord_inv>()) {
        rules::poly_ord_inv(deriv, prop.poly);
    }
    return true;
}

template <>
inline bool project_covering_properties<op::mccallum_filtered>(datastructures::CoveringRepresentation<PropertiesSet<op::mccallum_filtered>::type>& repr) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", repr);
    for (auto& cell_repr : repr.cells) {
        project_delineated_cell_properties<op::mccallum_filtered>(cell_repr, false);
    }
    auto cov = repr.get_covering();
    if (!rules::root_ordering_holds_filtered(repr.cells.front().derivation->underlying().sampled(), repr.ordering)) return false;
    rules::covering_holds(repr.cells.front().derivation->underlying().delineated(), cov, repr.ordering);
    return true;
}

template <>
inline bool project_delineation_properties<op::mccallum_filtered>(datastructures::DelineationRepresentation<PropertiesSet<op::mccallum_filtered>::type>& repr) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", repr);
    auto& deriv = *repr.derivation;

    for(const auto& prop : deriv.properties<properties::poly_irreducible_sgn_inv>()) {
        deriv.insert(properties::poly_pdel{ prop.poly });
        deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(prop.poly) });
    }

    for (const auto& poly : deriv.delin().nonzero()) {
        rules::poly_irrecubile_nonzero_sgn_inv(deriv, poly);
    }

    if (!rules::root_ordering_holds_filtered(deriv.underlying().sampled(), repr.ordering)) return false;

    for(const auto& prop : deriv.properties<properties::poly_irreducible_sgn_inv>()) {
        if (deriv.delin().nonzero().find(prop.poly) == deriv.delin().nonzero().end()) {
            rules::poly_irreducible_sgn_inv(deriv, repr.ordering, prop.poly);
        }
    }
    return true;
}

}
