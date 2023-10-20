#pragma once

#include "properties.h"
#include "../datastructures/derivation.h"

namespace smtrat::cadcells::operators::rules {

template<typename P>
void poly_irreducible_ord_inv_nullified(datastructures::SampledDerivation<P>& deriv, const datastructures::PolyRef& poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "ord_inv(" << poly << "), " << poly << " nullified");
    assert(deriv.proj().is_nullified(deriv.underlying_sample(), poly));

    boost::container::flat_set<datastructures::PolyRef> polys({poly});
    boost::container::flat_set<datastructures::PolyRef> poly_derivative;
    datastructures::PolyRef poly_nonzero_derivative_of_order;
    std::size_t order = 1;

    while (true) {
        for (const auto& p : polys) {
            if (deriv.proj().is_const(p)) continue;
            for (const auto v: deriv.proj().variables(p)) {
                auto d = deriv.proj().derivative(p, v);
                if (!deriv.proj().is_zero(deriv.sample(), d)) {
                    poly_nonzero_derivative_of_order = d;
                    poly_derivative.clear();
                } else {
                    poly_derivative.insert(d);
                }

                if (poly_nonzero_derivative_of_order != datastructures::PolyRef()) break;
            }
            if (poly_nonzero_derivative_of_order != datastructures::PolyRef()) break;
        }
        if (poly_nonzero_derivative_of_order != datastructures::PolyRef()) break;
        else order++;
        assert(!poly_derivative.empty()); // because order is finite
        polys = std::move(poly_derivative);
        poly_derivative = boost::container::flat_set<datastructures::PolyRef>();
    }

    deriv.insert(properties::cell_connected{ poly.level });
    deriv.insert(properties::poly_irreducible_sgn_inv{ poly_nonzero_derivative_of_order });
    for (const auto& p : polys) {
        deriv.insert(properties::poly_irreducible_sgn_inv{ p });
    }
}

template<typename P>
void poly_ord_inv_maybe_null(datastructures::SampledDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "ord_inv(" << poly << ")");
    if (deriv.proj().is_const(poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv(" << poly << ") <= " << poly << " const");
    } else {
        auto factors = deriv.proj().factors_nonconst(poly);
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv(" << poly << ") <= ord_inv(factors(" << poly << ")) <=> ord_inv(" << factors << ")");
        for (const auto& factor : factors) {
            if (deriv.proj().is_nullified(deriv.underlying_sample(), factor)) {
                poly_irreducible_ord_inv_nullified(deriv, factor);
            } else {
                poly_irreducible_ord_inv(deriv, factor);
            }
        }
    }   
}

}