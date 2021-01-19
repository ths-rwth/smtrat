#pragma once

#include "../datastructures/roots.h"

#include "properties.h"
#include "rules.h"
#include "delineation.h"
#include "operator.h"


namespace smtrat::cadcells::operators {

template <>
struct properties_set<op::mccallum> {
    using type = datastructures::properties<properties::poly_sgn_inv,properties::poly_irreducible_sgn_inv,properties::poly_ord_inv,properties::root_well_def,properties::poly_pdel>;
};

template <>
void project_basic_properties<op::mccallum>(datastructures::base_derivation<properties_set<op::mccallum>::type>& deriv) {
    for(const auto& prop : deriv.properties<properties::poly_sgn_inv>()) {
        rules::poly_sgn_inv(deriv, prop.poly);
    }
}

template <>
void delineate_properties<op::mccallum>(datastructures::base_derivation<properties_set<op::mccallum>::type>& deriv) {
    for(const auto& prop : deriv.properties<properties::poly_irreducible_sgn_inv>()) {
        delineation::delineate(deriv, prop);
    }
}

template <>
void project_delineated_cell_properties<op::mccallum>(datastructures::cell_representation<properties_set<op::mccallum>::type>& repr) {
    auto& deriv = *repr.derivation;

    for(const auto& prop : deriv.base()->properties<properties::poly_irreducible_sgn_inv>()) {
        if (repr.equational.find(prop.poly) == repr.equational.end()) {
            deriv.base()->insert(properties::poly_pdel{ prop.poly });
        }
    }

    for (const auto& poly : deriv.base()->delin().nonzero()) {
        if (repr.equational.find(poly) == repr.equational.end()) {
            rules::poly_irrecubile_nonzero_sgn_inv(*deriv.base(), poly);
        }
    }

    rules::cell_connected(deriv, repr.description);
    rules::cell_analytic_submanifold(deriv, repr.description);
    rules::cell_represents(deriv, repr.description);

    for (const auto& poly : repr.equational) {
        rules::poly_irrecubile_sgn_inv_ec(deriv, repr.description, poly);
    }

    rules::root_ordering_holds(*deriv.base()->underlying_cell(), repr.description, repr.ordering);

    for(const auto& prop : deriv.base()->properties<properties::poly_irreducible_sgn_inv>()) {
        if (repr.equational.find(prop.poly) == repr.equational.end() && deriv.base()->delin().nonzero().find(prop.poly) == deriv.base()->delin().nonzero().end()) {
            rules::poly_irrecubile_sgn_inv(deriv, repr.description, repr.ordering, prop.poly);
        }
    }
}

template <>
void project_cell_properties<op::mccallum>(datastructures::sampled_derivation<properties_set<op::mccallum>::type>& deriv) {
    for(const auto& prop : deriv.base()->properties<properties::root_well_def>()) {
        rules::root_well_def(deriv, prop.root);
    }
    for(const auto& prop : deriv.base()->properties<properties::poly_pdel>()) {
        rules::poly_pdel(deriv, prop.poly);
    }
    for(const auto& prop : deriv.base()->properties<properties::poly_ord_inv>()) {
        rules::poly_ord_inv(deriv, prop.poly);
    }
}

template <>
void project_covering_properties<op::mccallum>(datastructures::covering_representation<properties_set<op::mccallum>::type>& repr) {
    for (auto& cell_repr : repr.cells) {
        project_delineated_cell_properties<op::mccallum>(cell_repr);
    }
    rules::covering_holds(*datastructures::base_of(repr.cells.front().derivation->base()->underlying()), repr.get_covering());
}

}
