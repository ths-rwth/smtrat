#pragma once

namespace smtrat::cadcells::operators::rules::filter_util {

template<typename P>
void pseudo_order_invariant(datastructures::SampledDerivation<P>& deriv, const datastructures::PolyRef poly, const boost::container::flat_set<datastructures::PolyRef>& considered_polys) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "pseudo_ord_inv(" << poly << ") wrt " << considered_polys);
    auto subderiv = datastructures::make_derivation<P>(deriv.proj(), deriv.sample(), deriv.level()).delineated_ref();
    if (deriv.proj().is_const(poly)) return;
    for (const auto& factor : deriv.proj().factors_nonconst(poly)) {
        deriv.insert(properties::poly_ord_inv_base{ factor });
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> add ord_inv_base(" << factor << ") ");
        if (factor.level == deriv.level()) {
            if (deriv.proj().is_nullified(deriv.underlying_sample(), factor)) {
                deriv.insert(properties::poly_irreducible_sgn_inv{ factor });
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> add sgn_inv(" << factor << ") ");
            } else {
                auto roots = deriv.proj().real_roots(deriv.underlying_sample(), factor);
                if (roots.empty()) {
                    deriv.insert(properties::poly_irreducible_sgn_inv{ factor });
                    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> add sgn_inv(" << factor << ") ");
                } else {
                    if (considered_polys.contains(factor)) {
                        deriv.insert(properties::poly_additional_root_outside{ factor });
                        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> add additional_root_outside(" << factor << ") ");
                    } else {
                        deriv.insert(properties::poly_irreducible_sgn_inv{ factor });
                        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> add sgn_inv(" << factor << ") ");
                    }
                }
            }
        } else {
            assert(factor.level < deriv.level());
            deriv.insert(properties::poly_irreducible_sgn_inv{ factor });
            SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> add sgn_inv(" << factor << ") ");
        }
    }
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
    datastructures::RootMapPlain root_map;
    if (deriv.proj().is_const(poly)) return;
    for (const auto& factor : deriv.proj().factors_nonconst(poly)) {
        if (factor.level == deriv.level()) {
            if (deriv.proj().is_nullified(deriv.underlying_sample(), factor)) {
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> nullified: " << factor);
                deriv.delin().add_poly_nullified(factor);
            } else {
                auto roots = deriv.proj().real_roots(deriv.underlying_sample(), factor);
                if (roots.empty()) {
                    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> nonzero: " << factor);
                    deriv.delin().add_poly_nonzero(factor);
                } else {
                    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> got roots: " << roots);
                    for (size_t idx = 0; idx < roots.size(); idx++) {
                        root_map.try_emplace(roots[idx]).first->second.push_back(datastructures::IndexedRoot(factor, idx+1));
                    }
                }
            }
        }
    }
    for (const auto& entry : root_map) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "conisdering root " << entry);
        switch (filter_condition(entry.first)) {
        case result::NORMAL:
            for (const auto& ir : entry.second) {
                deriv.delin().add_root(entry.first, datastructures::TaggedIndexedRoot { ir, false, false, poly });
            }
            break;
        case result::INCLUSIVE:
            for (const auto& ir : entry.second) {
                deriv.delin().add_root(entry.first, datastructures::TaggedIndexedRoot { ir, true, false, poly });
            }
            break;
        case result::NORMAL_OPTIONAL:
            for (const auto& ir : entry.second) {
                deriv.delin().add_root(entry.first, datastructures::TaggedIndexedRoot { ir, false, true, poly });
            }
            break;
        case result::INCLUSIVE_OPTIONAL:
            for (const auto& ir : entry.second) {
                deriv.delin().add_root(entry.first, datastructures::TaggedIndexedRoot { ir, true, true, poly });
            }
            break;
        case result::OMIT:
            break;
        default:
            assert(false);
        }
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
