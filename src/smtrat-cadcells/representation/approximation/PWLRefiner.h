#pragma once

#include "pwl.h"
#include "ran_approximation.h"
#include <smtrat-cadcells/datastructures/roots.h>
#include <smtrat-common/types.h>

namespace smtrat::cadcells::representation::approximation {

inline std::size_t refine_if_necessary(
    PWLBuilder& pwlBuilder,
    std::size_t segment_index,
    const datastructures::IndexedRoot& ir,
    const Assignment& sample,
    const Assignment& underlying_sample,
    carl::LPPolynomial::ContextType& ctx,
    datastructures::Projections& proj,
    carl::Variable primary_variable,
    carl::Variable secondary_variable,
    bool below,
    int depth = 1
) {
    LinearSegment ls = pwlBuilder.get_segment(segment_index);
    datastructures::PolyRef poly_ref = ls.poly_ref(proj.polys(), ctx, primary_variable, secondary_variable);

    Assignment under_underlying_sample = underlying_sample;
    under_underlying_sample.erase(primary_variable);

    {
        datastructures::PolyRef res_ref = proj.res(poly_ref, ir.poly);
        if (res_ref.level <= under_underlying_sample.size()) return 0;

        std::vector<RAN> res_roots = proj.real_roots(under_underlying_sample, res_ref);
        if (std::all_of(res_roots.begin(), res_roots.end(),
            [&ls](const auto& root){ return root <= ls.domain().lower() || root >= ls.domain().upper(); }
        )) {
            return 0;
        }
    }

    Rational between = (ls.domain().lower() + ls.domain().upper()) / Rational(2);

    Assignment between_assignment = underlying_sample;
    between_assignment[primary_variable] = between;
    auto roots_between = proj.real_roots(between_assignment, ir.poly);

    assert(ir.index - 1 < roots_between.size());
    RAN bound_between = roots_between[ir.index - 1];

    Rational approximated_root = below ? rational_below(bound_between)
                                       : rational_above(bound_between);

    pwlBuilder.addPoint(between, approximated_root);

    if (depth == 0) { return 1; }

    return (
        refine_if_necessary(
            pwlBuilder,
            segment_index,
            ir, sample, underlying_sample, ctx, proj, primary_variable, secondary_variable, below,
            depth - 1
        ) +
        refine_if_necessary(
            pwlBuilder,
            segment_index + 1,
            ir, sample, underlying_sample, ctx, proj, primary_variable, secondary_variable, below,
            depth - 1
        )
    );
}


inline datastructures::RootFunction refine(
    PWLBuilder& pwlBuilder,
    const datastructures::IndexedRoot& ir,
    const Assignment& sample,
    const Assignment& underlying_sample,
    carl::LPPolynomial::ContextType& ctx,
    datastructures::Projections& proj,
    carl::Variable primary_variable,
    carl::Variable secondary_variable,
    bool below
) {
    for (std::size_t segment_index = 0; segment_index < pwlBuilder.get_number_of_segments(); ++segment_index) {
        segment_index += refine_if_necessary(
            pwlBuilder,
            segment_index,
            ir, sample, underlying_sample, ctx, proj, primary_variable, secondary_variable, below
        );
    }

    if (below) {
        return pwlBuilder.buildCompoundMaxMin(ctx, proj.polys(), primary_variable, secondary_variable);
    } else {
        return pwlBuilder.buildCompoundMinMax(ctx, proj.polys(), primary_variable, secondary_variable);
    }
}

}
