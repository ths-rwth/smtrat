#pragma once

#include "operator.h"


#include "../datastructures/roots.h"
#include "properties.h"
#include "rules.h"


namespace smtrat::cadcells::operators {

namespace mccallum_filtered_impl {

struct PropertiesSet {
    using type = datastructures::PropertiesT<properties::poly_sgn_inv,properties::poly_irreducible_sgn_inv,properties::poly_semi_sgn_inv,properties::poly_irreducible_semi_sgn_inv,properties::poly_ord_inv,properties::poly_del,properties::cell_connected,properties::poly_ord_inv_base,properties::root_ordering_holds>;
};

inline bool project_basic_properties(datastructures::SampledDerivation<PropertiesSet::type>& deriv, bool enable_weak = true) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", &deriv);
    for(const auto& prop : deriv.properties<properties::poly_del>()) {
        if (!rules::poly_del(deriv, prop.poly)) return false;
    }
    for(const auto& prop : deriv.properties<properties::poly_ord_inv>()) {
        rules::poly_ord_inv(deriv, prop.poly);
    }
    for(const auto& prop : deriv.properties<properties::poly_semi_sgn_inv>()) {
        if (enable_weak) {
            rules::poly_semi_sgn_inv(deriv, prop.poly);
        } else {
            deriv.insert(properties::poly_sgn_inv{prop.poly});
        }
    }
    for(const auto& prop : deriv.properties<properties::poly_sgn_inv>()) {
        rules::poly_sgn_inv(deriv, prop.poly);
    }
    return true;
}

inline void delineate_properties_common(datastructures::SampledDerivation<PropertiesSet::type>& deriv) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", &deriv);
    for(const auto& prop : deriv.properties<properties::poly_irreducible_sgn_inv>()) {
        rules::delineate(*deriv.delineated(), prop);
    }
    for(const auto& prop : deriv.properties<properties::poly_irreducible_semi_sgn_inv>()) {
        rules::delineate(*deriv.delineated(), prop);
    }
}

inline bool project_cell_properties(datastructures::CellRepresentation<PropertiesSet::type>& repr) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", repr );
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

inline bool project_covering_properties(datastructures::CoveringRepresentation<PropertiesSet::type>& repr) {
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

}

#define MCALLUMFILTEREDVARIANT(opname,enable_weak) \
    template <> \
    struct PropertiesSet<op::opname> { \
        using type = mccallum_filtered_impl::PropertiesSet::type; \
    }; \
    template <> \
    inline bool project_basic_properties<op::opname>(datastructures::SampledDerivation<PropertiesSet<op::opname>::type>& deriv) { \
        return mccallum_filtered_impl::project_basic_properties(deriv, enable_weak); \
    } \
    template <> \
    inline bool project_cell_properties<op::opname>(datastructures::CellRepresentation<PropertiesSet<op::opname>::type>& repr) { \
        return mccallum_filtered_impl::project_cell_properties(repr); \
    } \
    template <> \
    inline bool project_covering_properties<op::opname>(datastructures::CoveringRepresentation<PropertiesSet<op::opname>::type>& repr) { \
        return mccallum_filtered_impl::project_covering_properties(repr); \
    }

MCALLUMFILTEREDVARIANT(mccallum_filtered, false)
template <>
inline void delineate_properties<op::mccallum_filtered>(datastructures::SampledDerivation<PropertiesSet<op::mccallum_filtered>::type>& deriv) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", &deriv);
    mccallum_filtered_impl::delineate_properties_common(deriv);
    for(const auto& prop : deriv.properties<properties::root_ordering_holds>()) {
        rules::delineate_noop(deriv, prop);
    }
}

MCALLUMFILTEREDVARIANT(mccallum_filtered_all, false)
template <>
inline void delineate_properties<op::mccallum_filtered_all>(datastructures::SampledDerivation<PropertiesSet<op::mccallum_filtered_all>::type>& deriv) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", &deriv);
    mccallum_filtered_impl::delineate_properties_common(deriv);
    for(const auto& prop : deriv.properties<properties::root_ordering_holds>()) {
        rules::delineate_all(deriv, prop, {
            .only_rational_samples = false,
            .only_irreducible_resultants = false
        }, false);
    }
}

MCALLUMFILTEREDVARIANT(mccallum_filtered_all_ew, true)
template <>
inline void delineate_properties<op::mccallum_filtered_all_ew>(datastructures::SampledDerivation<PropertiesSet<op::mccallum_filtered_all_ew>::type>& deriv) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", &deriv);
    mccallum_filtered_impl::delineate_properties_common(deriv);
    for(const auto& prop : deriv.properties<properties::root_ordering_holds>()) {
        rules::delineate_all(deriv, prop, {
            .only_rational_samples = false,
            .only_irreducible_resultants = false
        }, true);
    }
}

MCALLUMFILTEREDVARIANT(mccallum_filtered_bounds_only, true)
template <>
inline void delineate_properties<op::mccallum_filtered_bounds_only>(datastructures::SampledDerivation<PropertiesSet<op::mccallum_filtered_bounds_only>::type>& deriv) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", &deriv);
    mccallum_filtered_impl::delineate_properties_common(deriv);
    for(const auto& prop : deriv.properties<properties::root_ordering_holds>()) {
        rules::delineate_bounds_only(deriv, prop);
    }
}

MCALLUMFILTEREDVARIANT(mccallum_filtered_onlyrat_ew, true)
template <>
inline void delineate_properties<op::mccallum_filtered_onlyrat_ew>(datastructures::SampledDerivation<PropertiesSet<op::mccallum_filtered_onlyrat_ew>::type>& deriv) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", &deriv);
    mccallum_filtered_impl::delineate_properties_common(deriv);
    for(const auto& prop : deriv.properties<properties::root_ordering_holds>()) {
        rules::delineate_all(deriv, prop, {
            .only_rational_samples = true,
            .only_irreducible_resultants = false
        }, true);
    }
}

MCALLUMFILTEREDVARIANT(mccallum_filtered_onlyrat_onlyirred_ew, true)
template <>
inline void delineate_properties<op::mccallum_filtered_onlyrat_onlyirred_ew>(datastructures::SampledDerivation<PropertiesSet<op::mccallum_filtered_onlyrat_onlyirred_ew>::type>& deriv) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", &deriv);
    mccallum_filtered_impl::delineate_properties_common(deriv);
    for(const auto& prop : deriv.properties<properties::root_ordering_holds>()) {
        rules::delineate_all(deriv, prop, {
            .only_rational_samples = true,
            .only_irreducible_resultants = true
        }, true);
    }
}

MCALLUMFILTEREDVARIANT(mccallum_filtered_onlyirred_ew, true)
template <>
inline void delineate_properties<op::mccallum_filtered_onlyirred_ew>(datastructures::SampledDerivation<PropertiesSet<op::mccallum_filtered_onlyirred_ew>::type>& deriv) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", &deriv);
    mccallum_filtered_impl::delineate_properties_common(deriv);
    for(const auto& prop : deriv.properties<properties::root_ordering_holds>()) {
        rules::delineate_all(deriv, prop, {
            .only_rational_samples = false,
            .only_irreducible_resultants = true
        }, true);
    }
}

MCALLUMFILTEREDVARIANT(mccallum_filtered_all_compound, false)
template <>
inline void delineate_properties<op::mccallum_filtered_all_compound>(datastructures::SampledDerivation<PropertiesSet<op::mccallum_filtered_all_compound>::type>& deriv) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", &deriv);
    mccallum_filtered_impl::delineate_properties_common(deriv);
    for(const auto& prop : deriv.properties<properties::root_ordering_holds>()) {
        rules::delineate_all_compound(deriv, prop, false, false);
    }
}

MCALLUMFILTEREDVARIANT(mccallum_filtered_all_compound_ew, true)
template <>
inline void delineate_properties<op::mccallum_filtered_all_compound_ew>(datastructures::SampledDerivation<PropertiesSet<op::mccallum_filtered_all_compound_ew>::type>& deriv) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", &deriv);
    mccallum_filtered_impl::delineate_properties_common(deriv);
    for(const auto& prop : deriv.properties<properties::root_ordering_holds>()) {
        rules::delineate_all_compound(deriv, prop, true, false);
    }
}

MCALLUMFILTEREDVARIANT(mccallum_filtered_all_compound_piecewiselinear, false)
template <>
inline void delineate_properties<op::mccallum_filtered_all_compound_piecewiselinear>(datastructures::SampledDerivation<PropertiesSet<op::mccallum_filtered_all_compound_piecewiselinear>::type>& deriv) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", &deriv);
    mccallum_filtered_impl::delineate_properties_common(deriv);
    for(const auto& prop : deriv.properties<properties::root_ordering_holds>()) {
        rules::delineate_compound_piecewiselinear(deriv, prop, false);
    }
}

MCALLUMFILTEREDVARIANT(mccallum_filtered_all_compound_piecewiselinear_ew, true)
template <>
inline void delineate_properties<op::mccallum_filtered_all_compound_piecewiselinear_ew>(datastructures::SampledDerivation<PropertiesSet<op::mccallum_filtered_all_compound_piecewiselinear_ew>::type>& deriv) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", &deriv);
    mccallum_filtered_impl::delineate_properties_common(deriv);
    for(const auto& prop : deriv.properties<properties::root_ordering_holds>()) {
        rules::delineate_compound_piecewiselinear(deriv, prop, true);
    }
}

MCALLUMFILTEREDVARIANT(mccallum_filtered_all_biggest_cell_ew, true)
template <>
inline void delineate_properties<op::mccallum_filtered_all_biggest_cell_ew>(datastructures::SampledDerivation<PropertiesSet<op::mccallum_filtered_all_biggest_cell_ew>::type>& deriv) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.operators", &deriv);
    mccallum_filtered_impl::delineate_properties_common(deriv);
    for(const auto& prop : deriv.properties<properties::root_ordering_holds>()) {
        rules::delineate_all_biggest_cell(deriv, prop, true);
    }
}

}
