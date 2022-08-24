#pragma once

namespace smtrat::cadcells::operators::rules::filter_util {

template<typename P>
void pseudo_order_invariant(datastructures::SampledDerivation<P>& deriv, const datastructures::PolyRef poly, const boost::container::flat_set<datastructures::PolyRef>& considered_polys) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "pseudo_ord_inv(" << poly << ") wrt " << considered_polys);
    auto subderiv = datastructures::make_derivation<P>(deriv.proj(), deriv.sample(), deriv.level()).sampled_ref();
    rules::poly_sgn_inv(*subderiv->delineated(), poly);
    for(const auto& prop : subderiv->template properties<properties::poly_irreducible_sgn_inv>()) {
        rules::delineate(*subderiv->delineated(), prop);
        deriv.insert(properties::poly_ord_inv_base{ prop.poly });
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> add pseudo_ord_inv(" << prop.poly << ") ");
    }
    for (const auto& r : subderiv->delin().roots()) {
        for (const auto& tir : r.second) {
            const auto& p = tir.root.poly;
            if (considered_polys.contains(p)) {
                deriv.insert(properties::poly_additional_root_outside{ p });
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> add additional_root_outside(" << p << ") ");
            } else {
                deriv.insert(properties::poly_irreducible_sgn_inv{ p });
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> add sgn_inv(" << p << ") ");
            }
        }
    }
    for (const auto& p : subderiv->delin().nonzero()) {
        deriv.insert(properties::poly_irreducible_sgn_inv{ p });
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> add sgn_inv(" << p << ") ");
    }
    for (const auto& p : subderiv->delin().nullified()) {
        deriv.insert(properties::poly_irreducible_sgn_inv{ p });
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> add sgn_inv(" << p << ") ");
    }
    deriv.underlying().sampled_ref()->merge_with(*subderiv->underlying().sampled_ref());
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> add sgn_inv for underlying polys");
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "pseudo_ord_inv end");
}

template<typename P>
std::optional<carl::Interval<RAN>> delineable_interval(datastructures::Projections& proj, const Assignment& sample, const std::vector<datastructures::PolyRef>& polys) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "delineable_interval start");
    auto subderiv = datastructures::make_derivation<P>(proj, sample, sample.size()).sampled_ref();
    for (const auto& poly : polys) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "delineable(" << poly << ") <= proj_del(" << poly << ") && sgn_inv(ldcf(" << poly << ") [" << proj.ldcf(poly) << "])");
        subderiv->insert(properties::poly_pdel{ poly });
        subderiv->insert(properties::poly_sgn_inv{ proj.ldcf(poly) });
    }
    for(const auto& prop : subderiv->template properties<properties::poly_pdel>()) {
        if (!rules::poly_pdel(*subderiv, prop.poly)) return std::nullopt;
    }
    for(const auto& prop : subderiv->template properties<properties::poly_ord_inv>()) {
        rules::poly_ord_inv(*subderiv, prop.poly);
    }
    for(const auto& prop : subderiv->template properties<properties::poly_sgn_inv>()) {
        rules::poly_sgn_inv(*subderiv->delineated(), prop.poly);
    }
    for(const auto& prop : subderiv->template properties<properties::poly_irreducible_sgn_inv>()) {
        rules::delineate(*subderiv->delineated(), prop);
    }
    subderiv->delineate_cell();
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "delineable_interval end; got " << subderiv->cell());

    if (subderiv->cell().is_section()) {
        return carl::Interval<RAN>(subderiv->cell().lower()->first);
    } else {
        return carl::Interval<RAN>(subderiv->cell().lower_unbounded() ? RAN(0) : subderiv->cell().lower()->first, subderiv->cell().lower_unbounded() ? carl::BoundType::INFTY : carl::BoundType::STRICT, subderiv->cell().upper_unbounded() ? RAN(0) : subderiv->cell().upper()->first, subderiv->cell().upper_unbounded() ? carl::BoundType::INFTY : carl::BoundType::STRICT);
    }
}

enum class result {
    NORMAL, INCLUSIVE, NORMAL_OPTIONAL, INCLUSIVE_OPTIONAL, OMIT
};

template<typename P>
void filter_roots(datastructures::DelineatedDerivation<P>& deriv, const datastructures::PolyRef poly, std::function<result(const RAN&)> filter_condition) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "filter_roots " << poly);
    auto subderiv = datastructures::make_derivation<P>(deriv.proj(), deriv.underlying_sample(), deriv.level()).delineated_ref();
    rules::poly_sgn_inv(*subderiv, poly);
    for(const auto& prop : subderiv->template properties<properties::poly_irreducible_sgn_inv>()) {
        rules::delineate(*subderiv, prop);
    }

    for (const auto& entry : subderiv->delin().roots()) {
        switch (filter_condition(entry.first)) {
        case result::NORMAL:
            for (const auto& ir : entry.second) {
                deriv.delin().add_root(entry.first, datastructures::TaggedIndexedRoot { ir.root });
            }
            break;
        case result::INCLUSIVE:
            for (const auto& ir : entry.second) {
                deriv.delin().add_root(entry.first, datastructures::TaggedIndexedRoot { ir.root, true });
            }
            break;
        case result::NORMAL_OPTIONAL:
            for (const auto& ir : entry.second) {
                deriv.delin().add_root(entry.first, datastructures::TaggedIndexedRoot { ir.root, false, true, poly });
            }
            break;
        case result::INCLUSIVE_OPTIONAL:
            for (const auto& ir : entry.second) {
                deriv.delin().add_root(entry.first, datastructures::TaggedIndexedRoot { ir.root, true, true, poly });
            }
            break;
        case result::OMIT:
            break;
        default:
            assert(false);
        }
    }
    for (const auto& p : subderiv->delin().nonzero()) {
        deriv.delin().add_poly_nonzero(p);
    }
    for (const auto& p : subderiv->delin().nullified()) {
        deriv.delin().add_poly_nullified(p);
    }
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "filter_roots end");
}

template<typename P>
auto projection_root(const datastructures::DelineatedDerivation<P>& deriv, const RAN& root) {
    Assignment ass = deriv.underlying_sample();
    ass.emplace(deriv.main_var(), root);
    return ass;
}

bool has_common_real_root(datastructures::Projections& proj, Assignment ass, const datastructures::PolyRef& poly1, const datastructures::PolyRef& poly2) {
    if (proj.is_nullified(ass,poly1) || proj.is_nullified(ass,poly2)) return true;
    auto roots1 = proj.real_roots(ass,poly1);
    auto roots2 = proj.real_roots(ass,poly2);
    auto common_zero = std::find_if(roots1.begin(), roots1.end(), [&roots2](const auto& root1) { return std::find(roots2.begin(), roots2.end(), root1) != roots2.end(); });
    return common_zero != roots1.end();
}


}
