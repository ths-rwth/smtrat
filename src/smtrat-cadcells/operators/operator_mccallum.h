#pragma once

#include "../datastructures/roots.h"

#include "properties.h"
#include "rules.h"
#include "operator.h"


namespace smtrat::cadcells::operators {

template <>
using properties<op::mccallum> = datastructures::properties<poly_sgn_inv,poly_irrecubile_sgn_inv,poly_ord_inv,root_well_def,poly_pdel>;

// TODO wie viel sinn hat diese funktion noch?
template <>
void project_basic_properties<op::mccallum>(derivation& deriv) {
    for(const auto& prop : properties.get<properties::poly_sgn_inv>()) {
        rules::poly_sgn_inv(deriv, prop.poly);
    }
}

template <>
delineation delineate_properties<op::mccallum>(derivation& deriv) {
    auto main_var = projections.var_order()[properties.level()-1];
    delineation del(main_var);
    for(const auto& prop : properties.get<properties::poly_irreducible_sgn_inv>()) {
        delineate(deriv, prop);
    }
    return del;
}

template <>
void project_delineated_cell_properties<op::mccallum>(derivation& deriv, const cell_representation& repr) {
    for(const auto& prop : deriv.properties<properties::poly_irreducible_sgn_inv>()) {
        if (repr->equational.find(prop.poly) == repr->equational.end()) {
            properties.insert(properties::poly_pdel{ poly });
        }
    }

    for (const auto& poly : del.nonzero()) {
        if (repr->equational.find(poly) == repr->equational.end()) {
            rules::poly_irrecubile_nonzero_sgn_inv(deriv.base_derivation(), poly);
        }
    }

    rules::cell_connected(deriv, repr->cell);
    rules::cell_analytic_submanifold(deriv, repr->cell);
    rules::cell_represents(deriv, repr->cell);

    for (const auto& poly : repr.equational) {
        rules::poly_irrecubile_sgn_inv_ec(deriv, repr->cell, poly);
    }

    rules::root_ordering_holds(deriv.underlying_cell(), repr->cell, repr->ordering);

    for(const auto& prop : properties.get<properties::poly_irreducible_sgn_inv>()) {
        if (repr.equational.find(prop.poly) == repr.equational.end() && del.nonzero().find(prop.poly) == del.nonzero().end()) {
            rules::poly_irrecubile_sgn_inv(deriv, repr->cell, repr->ordering, prop.poly);
        }
    }
}

template <>
void project_cell_properties<op::mccallum>(cell_derivation& deriv) {
    for(const auto& prop : properties.get<properties::root_well_def>()) {
        rules::root_well_def(deriv, prop.poly, prop.idx);
    }
    for(const auto& prop : properties.get<properties::poly_pdel>()) {
        rules::poly_pdel(deriv, prop.poly);
    }
    for(const auto& prop : properties.get<properties::poly_ord_inv>()) {
        rules::poly_ord_inv(deriv, prop.poly);
    }
}

// TODO woanders lösen?:
template <>
void project_covering_properties<op::mccallum>(datastructures::projections& projections, properties& properties, const assignment& sample, const covering_representation& repr) {
    // TODO project all cells:
    project_cell_properties<op:mccallum>

    // TODO project covering property
}

}
