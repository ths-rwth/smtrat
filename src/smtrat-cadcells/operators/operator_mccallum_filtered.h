#pragma once

#include "operator.h"


#include "../datastructures/roots.h"
#include "properties.h"
#include "rules.h"


namespace smtrat::cadcells::operators {


struct MccallumFilteredSettings {
    enum DelineationFunction {
        NOOP, ALL, BOUNDS_ONLY, COMPOUND, COMPOUND_PWL
    };
    static constexpr DelineationFunction delineation_function = NOOP;

    static constexpr bool enable_weak = false;

    // settings for delineate_all
    static constexpr bool only_rational_samples = false;
    static constexpr bool only_irreducible_resultants = false;
    static constexpr std::size_t only_if_total_degree_below = 0;
    static constexpr bool check_roots_outside_delin_int = false;
    static constexpr bool check_only_intersections_with_interval = false;
    static constexpr bool enable_intersections_with_interval = true;
    static constexpr bool use_sample_to_reduce_checks = true;

    // settings for delineate_all and delineate_bounds_only
    static constexpr bool only_if_no_intersections = false;

    static constexpr bool complete = false;
};

template<typename Settings>
struct MccallumFiltered {

static constexpr bool filter = true;

using PropertiesSet = datastructures::PropertiesT<properties::poly_sgn_inv,properties::poly_irreducible_sgn_inv,properties::poly_semi_sgn_inv,properties::poly_irreducible_semi_sgn_inv,properties::poly_ord_inv,properties::poly_del,properties::cell_connected,properties::poly_ord_inv_base,properties::root_ordering_holds,properties::poly_constraint_truth_inv,properties::iroot_constraint_truth_inv>;

static inline bool project_basic_properties(datastructures::SampledDerivation<PropertiesSet>& deriv) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", &deriv);

    if (Settings::complete) {
        for(const auto& prop : deriv.properties<properties::root_ordering_holds>()) {
            rules::root_ordering_holds_delineated_complete(deriv, prop.ordering);
        }
    }

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
        if (Settings::enable_weak) {
            rules::poly_semi_sgn_inv(deriv, prop.poly);
        } else {
            deriv.insert(properties::poly_sgn_inv{prop.poly});
        }
    }
    for(const auto& prop : deriv.properties<properties::poly_sgn_inv>()) {
        rules::poly_sgn_inv(deriv, prop.poly, !Settings::complete);
    }
    return true;
}

static inline void delineate_properties(datastructures::SampledDerivation<PropertiesSet>& deriv) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", &deriv);
    for(const auto& prop : deriv.properties<properties::poly_irreducible_sgn_inv>()) {
        rules::delineate(*deriv.delineated(), prop);
    }
    for(const auto& prop : deriv.properties<properties::poly_irreducible_semi_sgn_inv>()) {
        rules::delineate(*deriv.delineated(), prop);
    }
    for(const auto& prop : deriv.properties<properties::root_ordering_holds>()) {
        switch(Settings::delineation_function) {
            case MccallumFilteredSettings::ALL:
                rules::delineate_all<Settings>(deriv, prop, Settings::enable_weak);
                break;
            case MccallumFilteredSettings::BOUNDS_ONLY:
                rules::delineate_bounds_only<Settings>(deriv, prop);
                break;
            case MccallumFilteredSettings::COMPOUND:
                rules::delineate_all_compound(deriv, prop, Settings::enable_weak, false);
                break;
            case MccallumFilteredSettings::COMPOUND_PWL:
                rules::delineate_compound_piecewiselinear(deriv, prop, Settings::enable_weak);
                break;
            case MccallumFilteredSettings::NOOP:
            default:
                rules::delineate_noop(deriv, prop);
        }
    }
    for(const auto& prop : deriv.properties<properties::iroot_constraint_truth_inv>()) {
        rules::delineate(deriv, prop);
    }
    SMTRAT_STATISTICS_CALL(statistics().operator_delineate(deriv.level(), deriv.delin().num_roots(), deriv.delin().nullified().size(), deriv.delin().nonzero().size()));
}

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
    properties::insert_root_ordering_holds(deriv, repr.ordering);

    for(const auto& prop : deriv.properties<properties::root_ordering_holds>()) {
        if (!rules::root_ordering_holds_delineated(deriv, repr.description, repr.ordering, repr.ordering_polys, prop.ordering)) return false;
    }

    if (deriv.contains(properties::cell_connected{deriv.level()})) {
        rules::cell_connected(deriv, repr.description, repr.ordering);
    }
    rules::cell_analytic_submanifold(deriv, repr.description);
    rules::cell_represents(deriv, repr.description);

    if (!repr.equational.empty()) {
        deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(repr.description.section_defining().poly) });
    }

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

    for(const auto& prop : deriv.properties<properties::poly_ord_inv_base>()) {
        rules::poly_ord_inv_base(deriv, repr.description, repr.ordering, prop.poly);
    }
    for(const auto& prop : deriv.properties<properties::poly_irreducible_sgn_inv>()) {
        if (repr.equational.find(prop.poly) != repr.equational.end()) {
            rules::poly_irreducible_sgn_inv_ec(deriv, repr.description, prop.poly);
        } else if (deriv.delin().nonzero().find(prop.poly) != deriv.delin().nonzero().end()) {
            rules::poly_irreducible_nonzero_sgn_inv(*deriv.delineated(), prop.poly);
        } else if (deriv.delin().nullified().find(prop.poly) != deriv.delin().nullified().end()) {
            rules::poly_irreducible_null_sgn_inv(deriv, prop.poly);
        } else {
            rules::poly_irreducible_sgn_inv_filtered(deriv, repr.description, repr.ordering, prop.poly);
        }
    }
    for(const auto& prop : deriv.properties<properties::poly_irreducible_semi_sgn_inv>()) {
        if (repr.equational.find(prop.poly) != repr.equational.end()) {
            rules::poly_irreducible_semi_sgn_inv_ec(deriv, repr.description, prop.poly);
        } else if (deriv.delin().nonzero().find(prop.poly) != deriv.delin().nonzero().end()) {
            rules::poly_irreducible_nonzero_semi_sgn_inv(*deriv.delineated(), prop.poly);
        } else if (deriv.delin().nullified().find(prop.poly) != deriv.delin().nullified().end()) {
            rules::poly_irreducible_null_semi_sgn_inv(deriv, prop.poly);
        } else {
            rules::poly_irreducible_semi_sgn_inv_filtered(deriv, repr.description, repr.ordering, prop.poly);
        }
    }
    return true;
}

static inline bool project_covering_properties(datastructures::CoveringRepresentation<PropertiesSet>& repr) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", repr);
    for (auto& cell_repr : repr.cells) {
        if (!project_cell_properties(cell_repr)) {
            return false;
        }
    }
    auto cov = repr.get_covering();
    properties::insert_root_ordering_holds(repr.cells.front().derivation->underlying().sampled(), repr.ordering);
    rules::covering_holds(repr.cells.front().derivation->underlying().delineated(), cov, repr.ordering);
    return true;
}

};

}
