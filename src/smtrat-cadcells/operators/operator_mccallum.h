#pragma once

#include "operator.h"


#include "../datastructures/roots.h"
#include "properties.h"
#include "rules.h"

namespace smtrat::cadcells::operators {

struct MccallumSettings {
    static constexpr bool complete = false;
};

struct MccallumSettingsComplete : MccallumSettings {
    static constexpr bool complete = true;
};

template<typename Settings>

struct Mccallum {

static constexpr bool filter = false;

using PropertiesSet = datastructures::PropertiesT<properties::poly_sgn_inv,properties::poly_irreducible_sgn_inv,properties::poly_semi_sgn_inv,properties::poly_ord_inv,properties::poly_del,properties::cell_connected,properties::poly_constraint_truth_inv,properties::iroot_constraint_truth_inv>;

/**
 * Project basic cell properties.
 * 
 * Returns false iff the given operator is incomplete and cannot cover the given case (i.e. on nullification with McCallum).
 */
static inline bool project_basic_properties(datastructures::SampledDerivation<PropertiesSet>& deriv) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", &deriv);
    for(const auto& prop : deriv.properties<properties::poly_del>()) {
        if (!rules::poly_del(deriv, prop.poly)) return false;
    }
    for(const auto& prop : deriv.properties<properties::poly_ord_inv>()) {
        if (!Settings::complete) {
            rules::poly_ord_inv(deriv, prop.poly);
        } else {
            rules::poly_ord_inv_maybe_null(deriv, prop.poly);
        } 
    }
    for(const auto& prop : deriv.properties<properties::poly_constraint_truth_inv>()) {
        if (!rules::poly_constr_truth_inv(deriv, prop.constr)) return false;
    }
    for(const auto& prop : deriv.properties<properties::poly_semi_sgn_inv>()) {
        deriv.insert(properties::poly_sgn_inv{prop.poly});
    }
    for(const auto& prop : deriv.properties<properties::poly_sgn_inv>()) {
        rules::poly_sgn_inv(deriv, prop.poly, !Settings::complete);
    }
    return true;
}

/**
 * Delineate properties.
 */
static inline void delineate_properties(datastructures::SampledDerivation<PropertiesSet>& deriv) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", &deriv);
    for(const auto& prop : deriv.properties<properties::poly_irreducible_sgn_inv>()) {
        rules::delineate(*deriv.delineated(), prop);
    }
    for(const auto& prop : deriv.properties<properties::iroot_constraint_truth_inv>()) {
        rules::delineate(deriv, prop);
    }
}

/**
 * Project cell properties that depend on a delineation.
 */
static inline bool project_cell_properties(datastructures::CellRepresentation<PropertiesSet>& repr) {
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

    for(const auto& prop : deriv.properties<properties::iroot_constraint_truth_inv>()) {
        if (repr.equational.find(prop.constr.bound.poly) != repr.equational.end()) {
            // this is a hack:
            SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "truth_inv(" << prop.constr << ") <= the hack");
            assert(!deriv.proj().is_nullified(deriv.underlying_sample(), prop.constr.bound.poly));
            rules::poly_irreducible_sgn_inv_ec(deriv, repr.description, prop.constr.bound.poly);
            deriv.insert(operators::properties::poly_del{ prop.constr.bound.poly });
        } else if (deriv.delin().nonzero().find(prop.constr.bound.poly) != deriv.delin().nonzero().end()) {
            assert(false);
            return false;
        } else if (deriv.delin().nullified().find(prop.constr.bound.poly) != deriv.delin().nullified().end()) {
            assert(false);
            return false;
        } else {
            if (!rules::iroot_constr_truth_inv(deriv, repr.description, repr.ordering, prop.constr)) {
                assert(false);
                return false;
            }
        }
    }

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

/**
 * Project covering properties.
 */
static inline bool project_covering_properties(datastructures::CoveringRepresentation<PropertiesSet>& repr) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", repr);
    for (auto& cell_repr : repr.cells) {
        if (!project_cell_properties(cell_repr)) {
            return false;
        }
    }
    auto cov = repr.get_covering();
    rules::root_ordering_holds(repr.cells.front().derivation->underlying().sampled(), repr.ordering);
    rules::covering_holds(repr.cells.front().derivation->underlying().delineated(), cov, repr.ordering);
    return true;
}

};

}
