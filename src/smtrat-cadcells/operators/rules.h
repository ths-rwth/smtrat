#pragma once

#include "properties.h"
#include "delineation.h"
#include "../datastructures/derivation.h"

/**
 * Implementation of derivation rules.
 * 
 * Each rule is realized by a function which works on a derivation object. The parameters of the respective properties are passed as function parameter. The function realizing a derivation rule might either call other derivation rules or add properties to the given derivation.
 * 
 */
namespace smtrat::cadcells::operators::rules {

template<typename P>
void root_well_def(datastructures::SampledDerivation<P>& deriv, datastructures::IndexedRoot root) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "well_def(" << root << ", " << deriv.sample() << ")");
    assert(deriv.contains(properties::poly_pdel{ root.poly }));

    if (root.index != 1 && root.index != deriv.proj().num_roots(deriv.sample(), root.poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> well_def(" << root << ", " << deriv.sample() << ") <= proj_del(" << root.poly << ") && 0 < " << root << ".index < |real_roots(" << root.poly << "(" << deriv.sample() << "))|");
    } else if (deriv.proj().is_ldcf_zero(deriv.sample(), root.poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> well_def(" << root << ", " << deriv.sample() << ") <= proj_del(" << root.poly << ") && ldcf(" << root.poly << ")(" << deriv.sample() << ") = 0");
    } else {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> well_def(" << root << ", " << deriv.sample() << ") <= proj_del(" << root.poly << ") && sgn_inv(ldcf(" << root.poly << "))");
        deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(root.poly) });
    }
}

template<typename P>
bool is_trivial_root_well_def(datastructures::SampledDerivation<P>& deriv, datastructures::IndexedRoot root) {
    if (root.index != 1 && root.index != deriv.proj().num_roots(deriv.sample(), root.poly)) {
        return true;
    } else if (deriv.proj().is_ldcf_zero(deriv.sample(), root.poly)) {
        return true;
    } else {
        return false;
    }
}


template<typename P>
bool poly_non_null(datastructures::SampledDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "non_null(" << poly << ")");
    if(deriv.proj().is_nullified(deriv.sample(), poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "non_null(" << poly << ") <= false");
        return false;
    } else if (deriv.proj().has_const_coeff(poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "non_null(" << poly << ") <= " << poly << " has const coeff");
    } else if (!deriv.proj().is_ldcf_zero(deriv.sample(), poly) && deriv.contains(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) } )) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "non_null(" << poly << ") <= ldcf(" << poly << ")(" << deriv.sample() << ")!=0 && sgn_inv(ldcf(" << poly << ") [" << deriv.proj().ldcf(poly) << "])");
    } else if (
        /* deriv.proj().know_disc(poly) && */ deriv.proj().degree(poly) > 1 && !deriv.proj().is_disc_zero(deriv.sample(), poly) &&
        (deriv.contains(properties::poly_sgn_inv{ deriv.proj().disc(poly) }) || deriv.contains(properties::poly_ord_inv{ deriv.proj().disc(poly) }))
    ) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "non_null(" << poly << ") <= disc(" << poly << ")(" << deriv.sample() << ")!=0 && sgn_inv(disc(" << poly << ") [" << deriv.proj().disc(poly) << "])");
    } else {
        auto coeff = deriv.proj().simplest_nonzero_coeff(deriv.sample(), poly, [&](const Polynomial& a, const Polynomial& b) {
            if (deriv.proj().known(a) && deriv.contains( properties::poly_sgn_inv { deriv.proj().polys()(a)} )) return true;
            if (deriv.proj().known(b) && deriv.contains( properties::poly_sgn_inv { deriv.proj().polys()(b)} )) return true;
            return carl::level_of(a) < carl::level_of(b) || (carl::level_of(a) == carl::level_of(b) && a.degree() < b.degree());
        });
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "non_null(" << poly << ") <= sgn_inv(" << coeff << ") && " << coeff << " in coeff(" << poly << ")");
        deriv.insert(properties::poly_sgn_inv{ coeff });
    }
    return true;
}

template<typename P>
bool poly_pdel(datastructures::SampledDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "proj_del(" << poly << ")");
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> proj_del(" << poly << ") <= non_null(" << poly << ") && ord_inv(disc(" << poly << ") [" << deriv.proj().disc(poly) << "]) && cell_connected(" << (poly.level-1) << ")");
    deriv.insert(properties::poly_ord_inv{ deriv.proj().disc(poly) });
    deriv.insert(properties::cell_connected{ poly.level-1 });
    if (!poly_non_null(deriv, poly)) return false;
    return true;
}

template<typename P>
void poly_irrecubile_ord_inv(datastructures::SampledDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "ord_inv(" << poly << "), " << poly << " irreducible");
    if (deriv.proj().is_const(poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv(" << poly << ") <= " << poly << " const");
    } else {
        if (deriv.proj().is_zero(deriv.sample(), poly)) {
            SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv(" << poly << ") <= proj_del(" << poly << ") && sgn_inv(" << poly << ") && cell_connected(" << poly.level << ")");
            deriv.insert(properties::poly_pdel{ poly });
            deriv.insert(properties::cell_connected{ poly.level });
        } else {
            SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv(" << poly << ") <= " << poly << "(" << deriv.sample() << ") != 0 && sgn_inv(" << poly << ")");
        }
        deriv.insert(properties::poly_irreducible_sgn_inv{ poly });
    }
}

template<typename P>
void poly_ord_inv(datastructures::SampledDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "ord_inv(" << poly << ")");
    if (deriv.proj().is_const(poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv(" << poly << ") <= " << poly << " const");
    } else {
        auto factors = deriv.proj().factors_nonconst(poly);
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv(" << poly << ") <= ord_inv(factors(" << poly << ")) <=> ord_inv(" << factors << ")");
        for (const auto& factor : factors) {
            poly_irrecubile_ord_inv(deriv, factor);
        }
    }   
}

template<typename P>
void poly_irrecubile_ord_inv(datastructures::BaseDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "ord_inv(" << poly << "), " << poly << " irreducible");
    if (deriv.proj().is_const(poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv(" << poly << ") <= " << poly << " const");
    } else {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv(" << poly << ") <= proj_del(" << poly << ") && sgn_inv(" << poly << ") && cell_connected(" << poly.level << ")");
        deriv.insert(properties::poly_pdel{ poly });
        deriv.insert(properties::cell_connected{ poly.level });
        deriv.insert(properties::poly_irreducible_sgn_inv{ poly });
    }
}

template<typename P>
void poly_ord_inv(datastructures::BaseDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "ord_inv(" << poly << ")");
    auto factors = deriv.proj().factors_nonconst(poly);
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv(" << poly << ") <= ord_inv(factors(" << poly << ")) <=> ord_inv(" << factors << ")");
    for (const auto& factor : factors) {
        poly_irrecubile_ord_inv(deriv, factor);
    }
}

template<typename P>
void poly_sgn_inv(datastructures::DelineatedDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "sgn_inv(" << poly << ")");
    if (deriv.proj().is_const(poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> sgn_inv(" << poly << ") <= " << poly << " const");
    } else if (deriv.contains(properties::poly_ord_inv{ poly })) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> sgn_inv(" << poly << ") <= ord_inv(" << poly << ")");
    } else {
        auto factors = deriv.proj().factors_nonconst(poly);
        for (const auto& factor : factors) {
            if (factor.level < poly.level && deriv.proj().is_zero(deriv.underlying_sample(), factor)) {
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> sgn_inv(" << poly << ") <= sgn_inv(" << factor << ") && "<< factor <<"("<< deriv.underlying_sample() <<")=0");
                deriv.insert(properties::poly_irreducible_sgn_inv{ factor });
                return;
            }
        }

        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> sgn_inv(" << poly << ") <= sgn_inv(factors(" << poly << ")) <=> sgn_inv(" << factors << ")");
        for (const auto& factor : factors) {
            deriv.insert(properties::poly_irreducible_sgn_inv{ factor });
        }
    }
}

template<typename P>
void poly_irrecubile_nonzero_sgn_inv(datastructures::DelineatedDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "sgn_inv(" << poly << "), " << poly << " irreducible and non-zero");
    assert(deriv.proj().num_roots(deriv.underlying_sample(), poly) == 0);
    deriv.insert(properties::poly_pdel{ poly });
    if (deriv.proj().is_ldcf_zero(deriv.underlying_sample(), poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> sgn_inv(" << poly << ") <= proj_del(" << poly << ") && sgn_inv(ldcf(" << poly << ") [" << deriv.proj().ldcf(poly) << "])");
        deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) });
    } else {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> sgn_inv(" << poly << ") <= proj_del(" << poly << ")");
    }
}

template<typename P>
void cell_connected(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& cell, const datastructures::IndexedRootOrdering& ordering) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "connected(" << deriv.level() << ")");
    if (!cell.is_section() && !cell.lower().is_infty() && !cell.upper().is_infty() && cell.lower().value().poly != cell.upper().value().poly) {
        assert(deriv.contains(properties::poly_pdel{ cell.lower().value().poly }));
        assert(deriv.contains(properties::poly_pdel{ cell.upper().value().poly }));
        assert(ordering.leq_transitive(cell.lower().value(),cell.upper().value()));
    }
    deriv.insert(properties::cell_connected{ deriv.level()-1 });
}

template<typename P>
void cell_analytic_submanifold([[maybe_unused]] datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval&) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "an_sub(" << deriv.level() << ")");
}

template<typename P>
void poly_irreducible_sgn_inv_ec(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& cell, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "sgn_inv(" << poly << "), using EC");
    assert(cell.is_section());
    assert(deriv.contains(properties::poly_pdel{ cell.section_defining().poly }));
    assert(deriv.contains(properties::poly_sgn_inv{ deriv.proj().ldcf(cell.section_defining().poly) }));
    deriv.insert(properties::cell_connected{ poly.level-1 });
    if (cell.section_defining().poly != poly) {
        deriv.insert(properties::poly_ord_inv{ deriv.proj().res(cell.section_defining().poly, poly) });
    }
}

template<typename P>
void root_represents(datastructures::SampledDerivation<P>& deriv, datastructures::IndexedRoot root) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "ir_rep(" << root << ", " << deriv.sample() << ")");
    assert(deriv.contains(properties::poly_pdel{ root.poly }));
    deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(root.poly) });
}

template<typename P>
void cell_represents(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& cell) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "repr(" << cell << ")");
    if (!cell.is_section()) {
        if (!cell.lower().is_infty()) {
            root_represents(deriv, cell.lower().value());
        }
        if (!cell.upper().is_infty()) {
            root_represents(deriv, cell.upper().value());
        }
    } else {
        root_represents(deriv, cell.section_defining());
    }
}

template<typename P>
void cell_well_def(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& cell) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "well_def(" << cell << ")");
    if (!cell.is_section()) {
        if (!cell.lower().is_infty()) {
            deriv.insert(properties::root_well_def{ cell.lower().value() });
        }
        if (!cell.upper().is_infty()) {
            deriv.insert(properties::root_well_def{ cell.upper().value() });
        }
    } else {
        deriv.insert(properties::root_well_def{ cell.section_defining() });
    }
}

template<typename P>
void root_ordering_holds(datastructures::SampledDerivation<P>& deriv, const datastructures::IndexedRootOrdering& ordering) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "ir_ord(" << ordering << ", " << deriv.sample() << ")");
    deriv.insert(properties::cell_connected{ deriv.level() });
    for (const auto& rel : ordering.data()) {
        if (rel.first.poly != rel.second.poly) {
            assert(deriv.contains(properties::poly_pdel{ rel.first.poly }));
            assert(deriv.contains(properties::poly_pdel{ rel.second.poly }));
            deriv.insert(properties::poly_ord_inv{ deriv.proj().res(rel.first.poly, rel.second.poly) });
        }
    }
}

namespace filter_util {
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
            delineation::delineate(*subderiv->delineated(), prop);
        }
        subderiv->delineate_cell();
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "delineable_interval end; got " << subderiv->cell());

        if (subderiv->cell().is_section()) {
            return carl::Interval<RAN>(subderiv->cell().lower()->first);
        } else {
            return carl::Interval<RAN>(subderiv->cell().lower_unbounded() ? RAN(0) : subderiv->cell().lower()->first, subderiv->cell().lower_unbounded() ? carl::BoundType::INFTY : carl::BoundType::STRICT, subderiv->cell().upper_unbounded() ? RAN(0) : subderiv->cell().upper()->first, subderiv->cell().upper_unbounded() ? carl::BoundType::INFTY : carl::BoundType::STRICT);
        }
    }

    template<typename P>
    void filter_resultant(datastructures::SampledDerivation<P>& deriv, const datastructures::PolyRef poly1, const datastructures::PolyRef poly2, std::function<bool(const RAN&)> filter_condition) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "filter_resultant start; resultant is " << deriv.proj().res(poly1, poly2));
        auto subderiv = datastructures::make_derivation<P>(deriv.proj(), deriv.sample(), deriv.level()).sampled_ref();
        subderiv->insert(properties::poly_ord_inv{ deriv.proj().res(poly1, poly2) });
        // TODO what happens if a level is skipped? should we jump to the resultant's level?
        for(const auto& prop : subderiv->template properties<properties::poly_ord_inv>()) {
            // this will make all polynomials projectively delineable.
            // TODO later: we need to defer making a poly projectively delineable to the point for the case we want to apply equational constraints 
            // TODO later: do we need this even for polys without a relevant root?
            rules::poly_ord_inv(*subderiv->base(), prop.poly);
        }
        for(const auto& prop : subderiv->template properties<properties::poly_sgn_inv>()) {
            rules::poly_sgn_inv(*subderiv->delineated(), prop.poly);
        }
        for(const auto& prop : subderiv->template properties<properties::poly_irreducible_sgn_inv>()) {
            delineation::delineate(*subderiv->delineated(), prop);
        }

        for (const auto& entry : subderiv->delin().roots()) {
            if (filter_condition(entry.first)) {
                for (const auto root : entry.second) {
                    deriv.insert(properties::root_inv{ root });
                    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "add " << properties::root_inv{ root });
                }
            } else {
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "skip " << entry.first << " / " << entry.second);
            }
        }

        deriv.underlying().sampled_ref()->merge_with(*subderiv->underlying().sampled_ref());

        // TODO later: can we ignore the following?
        for (const auto& p : subderiv->delin().nonzero()) {
            deriv.insert(properties::poly_irreducible_sgn_inv{ p });
        }
        for (const auto& p : subderiv->delin().nullified()) {
            deriv.insert(properties::poly_irreducible_sgn_inv{ p });
        }
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "filter_resultant end");
    }

    template<typename P>
    auto projection_root(const datastructures::SampledDerivation<P>& deriv, const RAN& root) {
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

template<typename P>
bool root_ordering_holds_filtered(datastructures::SampledDerivation<P>& deriv, const datastructures::IndexedRootOrdering& ordering) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "ir_ord(" << ordering << ", " << deriv.sample() << ")");
    deriv.insert(properties::cell_connected{ deriv.level() });

    boost::container::flat_map<datastructures::PolyRef,boost::container::flat_map<datastructures::PolyRef,std::vector<std::pair<datastructures::IndexedRoot, datastructures::IndexedRoot>>>> decomposed;

    for (const auto& rel : ordering.data()) {
        if (rel.first.poly != rel.second.poly) {
            if (rel.first.poly < rel.second.poly) {
                decomposed.try_emplace(rel.first.poly).first->second.try_emplace(rel.second.poly).first->second.push_back(rel);
            } else {
                decomposed.try_emplace(rel.second.poly).first->second.try_emplace(rel.first.poly).first->second.push_back(rel);
            }
        }
    }

    for (const auto& d1 : decomposed) {
        const auto& poly1 = d1.first;
        for (const auto& d2 : d1.second) {
            const auto& poly2 = d2.first;
            SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "consider pair " << poly1 << " and " << poly2 << "");
            assert(deriv.contains(properties::poly_pdel{ poly1 }));
            assert(deriv.contains(properties::poly_pdel{ poly2 }));
            auto delineable_interval = filter_util::delineable_interval<P>(deriv.proj(), deriv.sample(), std::vector<datastructures::PolyRef>({ poly1, poly2 }));
            if (!delineable_interval) return false;
            filter_util::filter_resultant(deriv, poly1, poly2, [&](const RAN& ran) {
                Assignment ass = filter_util::projection_root(deriv, ran);
                if (!delineable_interval->contains(ran)) {
                    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> resultant's root " << ran << " outside of " << delineable_interval);
                    return filter_util::has_common_real_root(deriv.proj(),ass,poly1,poly2);
                } else {
                    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> resultant's root " << ran << " in " << delineable_interval);
                    assert(!deriv.proj().is_nullified(ass,poly1));
                    assert(!deriv.proj().is_nullified(ass,poly2));
                    auto roots1 = deriv.proj().real_roots(ass,poly1);
                    auto roots2 = deriv.proj().real_roots(ass,poly2);
                    for (const auto& pair : d2.second) {
                        auto index1 = pair.first.poly == poly1 ? pair.first.index : pair.second.index;
                        auto index2 = pair.first.poly == poly1 ? pair.second.index : pair.first.index;
                        assert(index1 <= roots1.size());
                        assert(index2 <= roots2.size());
                        if (roots1[index1-1] == roots2[index2-1]) {
                            SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> common root at " << ran);
                            return true;
                        }
                    }
                    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> no common at " << ran);
                    return false;
                }
            });
        }
    }
    return true;
}

namespace poly_irreducible_sgn_inv_util {
    inline boost::container::flat_set<datastructures::PolyRef> resultant_polys(const datastructures::PolyRef& poly, const datastructures::IndexedRootOrdering& ordering) {
        boost::container::flat_set<datastructures::PolyRef> result;
        for (const auto& rel : ordering.data()) {
            if (rel.first.poly == poly) {
                result.insert(rel.second.poly);
            } else if (rel.second.poly == poly) {
                result.insert(rel.first.poly);
            }
        }
        return result;
    }
            
    template<typename P>
    inline std::optional<datastructures::IndexedRoot> protect_lower(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& cell, const datastructures::IndexedRootOrdering& ordering, const datastructures::PolyRef& poly, const boost::container::flat_set<datastructures::PolyRef>& res_polys) {
        if (poly == cell.lower().value().poly) return cell.lower().value();

        // check if a res_poly has a well defined root below
        for (const auto& res_poly : res_polys) {
            if (res_poly == cell.lower().value().poly) {
                return cell.lower().value();
            } else {
                auto res_lower_root = ordering.leq_transitive(res_poly, cell.lower().value());
                if (res_lower_root) {
                    if (deriv.contains(properties::root_well_def{*res_lower_root}) || is_trivial_root_well_def(deriv.underlying().sampled(), *res_lower_root)) {
                        return res_lower_root;
                    }
                }
            }
        }

        auto lower_root = ordering.leq_transitive(poly, cell.lower().value());
        if (lower_root) return lower_root;
        return std::nullopt;
    }

    template<typename P>
    inline std::optional<datastructures::IndexedRoot> protect_upper(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& cell, const datastructures::IndexedRootOrdering& ordering, const datastructures::PolyRef& poly, const boost::container::flat_set<datastructures::PolyRef>& res_polys) {
        if (poly == cell.upper().value().poly) return cell.upper().value();

        // check if a res_poly has a well defined root above
        for (const auto& res_poly : res_polys) {
            if (res_poly == cell.upper().value().poly) {
                return cell.upper().value();
            } else {
                auto res_upper_root = ordering.leq_transitive(cell.upper().value(), res_poly);
                if (res_upper_root) {
                    if (deriv.contains(properties::root_well_def{*res_upper_root}) || is_trivial_root_well_def(deriv.underlying().sampled(), *res_upper_root)) {
                        return res_upper_root;
                    }
                }
            }
        }

        auto upper_root = ordering.leq_transitive(cell.upper().value(), poly);
        if (upper_root) return upper_root;
        return std::nullopt;
    }
}

template<typename P>
void poly_irreducible_sgn_inv(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& cell, const datastructures::IndexedRootOrdering& ordering, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "sgn_inv(" << poly << "), " << poly << " irreducible");
    assert(!deriv.proj().is_nullified(deriv.underlying_sample(), poly));
    assert(deriv.contains(properties::poly_pdel{ poly }));
    deriv.insert(properties::cell_connected{ poly.level-1 });
    if (cell.is_section() && deriv.proj().is_zero(deriv.sample(), poly)) {
        // ok by indexed root ordering!
    } else {
        assert(!deriv.proj().is_zero(deriv.sample(), poly));
        if (!cell.is_section() && (cell.lower().is_infty() || cell.upper().is_infty())) {
            deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) });
        } else {
            assert(cell.is_section() || (cell.lower().is_strict() && cell.upper().is_strict()));

            // compute set of polynomials that have a resultant with the current polynomials (according to the given ordering)
            boost::container::flat_set<datastructures::PolyRef> res_polys = poly_irreducible_sgn_inv_util::resultant_polys(poly, ordering);
            
            auto lower = poly_irreducible_sgn_inv_util::protect_lower(deriv, cell, ordering, poly, res_polys);
            auto upper = poly_irreducible_sgn_inv_util::protect_upper(deriv, cell, ordering, poly, res_polys);
            
            if (!lower || !upper) {
                deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) });
            } else {
                deriv.insert(properties::root_well_def{*lower});
                if (lower->poly != poly) {
                    assert(deriv.contains(properties::poly_ord_inv{ deriv.proj().res(lower->poly, poly) }));
                }
                deriv.insert(properties::root_well_def{*upper});
                if (upper->poly != poly) {
                    assert(deriv.contains(properties::poly_ord_inv{ deriv.proj().res(upper->poly, poly) }));
                }
            }
        }
    }
}

template<typename P>
bool poly_irreducible_sgn_inv_filtered(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& cell, const datastructures::IndexedRootOrdering& ordering, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "sgn_inv(" << poly << "), " << poly << " irreducible");
    assert(!deriv.proj().is_nullified(deriv.underlying_sample(), poly));
    assert(deriv.contains(properties::poly_pdel{ poly }));
    deriv.insert(properties::cell_connected{ poly.level-1 });
    if (cell.is_section() && deriv.proj().is_zero(deriv.sample(), poly)) {
        // ok by indexed root ordering!
    } else {
        assert(!deriv.proj().is_zero(deriv.sample(), poly));
        if (!cell.is_section() && (cell.lower().is_infty() || cell.upper().is_infty())) {
            deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) });
        } else {
            assert(cell.is_section() || (cell.lower().is_strict() && cell.upper().is_strict()));

            // compute set of polynomials that have a resultant with the current polynomials (according to the given ordering)
            boost::container::flat_set<datastructures::PolyRef> res_polys = poly_irreducible_sgn_inv_util::resultant_polys(poly, ordering);
            
            auto lower = poly_irreducible_sgn_inv_util::protect_lower(deriv, cell, ordering, poly, res_polys);
            auto upper = poly_irreducible_sgn_inv_util::protect_upper(deriv, cell, ordering, poly, res_polys);
            
            if (!lower || !upper) {
                deriv.insert(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) });
            } else {
                deriv.insert(properties::root_well_def{*lower});
                if (lower->poly != poly) {
                    auto delineable_interval = filter_util::delineable_interval<P>(deriv.proj(), deriv.sample(), std::vector<datastructures::PolyRef>({ cell.lower().value().poly }));
                    if (!delineable_interval) return false;
                    filter_util::filter_resultant(deriv, lower->poly, poly, [&](const RAN& ran) {
                        Assignment ass = filter_util::projection_root(deriv, ran);
                        if (delineable_interval->contains(ran)) {
                            if (deriv.proj().is_nullified(ass,lower->poly) || deriv.proj().is_nullified(ass,poly)) return true;
                            auto roots1 = deriv.proj().real_roots(ass,lower->poly);
                            auto roots2 = deriv.proj().real_roots(ass,poly);
                            assert(!deriv.proj().is_nullified(ass,cell.lower().value().poly));
                            auto root_lo = deriv.proj().real_roots(ass,cell.lower().value().poly).at(cell.lower().value().index-1);
                            auto common_zero = std::find_if(roots1.begin(), roots1.end(), [&roots2](const auto& root1) { return std::find(roots2.begin(), roots2.end(), root1) != roots2.end(); });
                            return (common_zero != roots1.end() && *common_zero <= ran);
                        } else {
                            return filter_util::has_common_real_root(deriv.proj(),ass,lower->poly, poly);
                        }                   
                    });
                }
                deriv.insert(properties::root_well_def{*upper});
                if (upper->poly != poly) {
                    auto delineable_interval = filter_util::delineable_interval<P>(deriv.proj(), deriv.sample(), std::vector<datastructures::PolyRef>({ cell.upper().value().poly }));
                    if (!delineable_interval) return false;
                    filter_util::filter_resultant(deriv, upper->poly, poly, [&](const RAN& ran) {
                        Assignment ass = filter_util::projection_root(deriv, ran);
                        if (delineable_interval->contains(ran)) {
                            if (deriv.proj().is_nullified(ass,upper->poly) || deriv.proj().is_nullified(ass,poly)) return true;
                            auto roots1 = deriv.proj().real_roots(ass,upper->poly);
                            auto roots2 = deriv.proj().real_roots(ass,poly);
                            assert(!deriv.proj().is_nullified(ass,cell.upper().value().poly));
                            auto root_up = deriv.proj().real_roots(ass, cell.upper().value().poly).at(cell.upper().value().index-1);
                            auto common_zero = std::find_if(roots1.begin(), roots1.end(), [&roots2](const auto& root1) { return std::find(roots2.begin(), roots2.end(), root1) != roots2.end(); });
                            return (common_zero != roots1.end() && *common_zero >= ran);
                        } else {
                            return filter_util::has_common_real_root(deriv.proj(),ass,upper->poly, poly);
                        }                     
                    });
                }
            }
        }
    }
    return true;
}

template<typename P>
void root_inv(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& /*cell*/, const datastructures::IndexedRootOrdering& /*ordering*/, datastructures::IndexedRoot root) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "root_inv(" << root << ")");
    assert(deriv.contains(properties::poly_pdel{ root.poly }));
    // guaranteed by ordering
    deriv.insert(properties::root_well_def{root});
}

template<typename P>
void poly_irreducible_sgn_inv(datastructures::DelineatedDerivation<P>& deriv, const datastructures::IndexedRootOrdering& /*ordering*/, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "sgn_inv(" << poly << "), " << poly << " irreducible");
    assert(deriv.contains(properties::poly_pdel{ poly }));
    assert(deriv.contains(properties::poly_sgn_inv{ deriv.proj().ldcf(poly) }));
    // guaranteed by ordering
}

template<typename P>
void covering_holds(datastructures::DelineatedDerivation<P>& deriv, const datastructures::CoveringDescription& covering, const datastructures::IndexedRootOrdering& ordering) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "holds(" << covering << ")");
    for (auto it = covering.cells().begin(); it != covering.cells().end()-1; it++) {
        assert(deriv.contains(properties::root_well_def{ it->upper().value() }));
        assert(deriv.contains(properties::root_well_def{ std::next(it)->lower().value() }));
        assert(ordering.leq_transitive(std::next(it)->lower().value(), it->upper().value()));
    }
}

}