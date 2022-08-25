#pragma once

#include "rules_filter_util.h"

namespace smtrat::cadcells::operators::rules {

namespace ordering_util {
    inline auto decompose(const datastructures::IndexedRootOrdering& ordering) {
        boost::container::flat_map<std::pair<datastructures::PolyRef,datastructures::PolyRef>,std::vector<datastructures::IndexedRootRelation>> result;
        for (const auto& rel : ordering.data()) {
            if (rel.first.poly != rel.second.poly) {
                if (rel.first.poly < rel.second.poly) {
                    result.try_emplace(std::make_pair(rel.first.poly, rel.second.poly)).first->second.push_back(rel);
                } else {
                    result.try_emplace(std::make_pair(rel.second.poly, rel.first.poly)).first->second.push_back(rel);
                }
            }
        }
        return result;
    }
}

template<typename P>
void delineate(datastructures::SampledDerivation<P>& deriv, const properties::root_ordering_holds& prop) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "delineate(" << prop << ")");

    auto decomposed = ordering_util::decompose(prop.ordering);
    for (const auto& d : decomposed) {
        const auto& poly1 = d.first.first;
        const auto& poly2 = d.first.second;
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "consider pair " << poly1 << " and " << poly2 << "");
        bool all_relations_weak = std::find_if(d.second.begin(), d.second.end(), [](const auto& pair){ return pair.is_strict; }) == d.second.end();
        auto delineable_interval = filter_util::delineable_interval<P>(deriv.proj(), deriv.sample(), std::vector<datastructures::PolyRef>({ poly1, poly2 }));
        assert(delineable_interval);
        filter_util::filter_roots(*deriv.delineated(), deriv.proj().res(poly1, poly2), [&](const RAN& ran) {
            Assignment ass = filter_util::projection_root(*deriv.delineated(), ran);
            if (!delineable_interval->contains(ran)) {
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> resultant's root " << ran << " outside of " << delineable_interval);
                if (filter_util::has_common_real_root(deriv.proj(),ass,poly1,poly2)) {
                    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> common root at " << ran);
                    if (all_relations_weak) return filter_util::result::INCLUSIVE;
                    else return filter_util::result::NORMAL;
                } else {
                    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> omit root " << ran);
                    return filter_util::result::OMIT;
                }
            } else {
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> resultant's root " << ran << " in " << delineable_interval);
                assert(!deriv.proj().is_nullified(ass,poly1));
                assert(!deriv.proj().is_nullified(ass,poly2));
                auto roots1 = deriv.proj().real_roots(ass,poly1);
                auto roots2 = deriv.proj().real_roots(ass,poly2);
                for (const auto& pair : d.second) {
                    auto index1 = pair.first.poly == poly1 ? pair.first.index : pair.second.index;
                    auto index2 = pair.first.poly == poly1 ? pair.second.index : pair.first.index;
                    assert(index1 <= roots1.size());
                    assert(index2 <= roots2.size());
                    if (roots1[index1-1] == roots2[index2-1]) {
                        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> relevant intersection at " << ran);
                        if (all_relations_weak) return filter_util::result::INCLUSIVE;
                        else return filter_util::result::NORMAL;
                        // if (pair.is_strict) return filter_util::result::INCLUSIVE;
                        // else return filter_util::result::NORMAL;
                    }
                }
                if (filter_util::has_common_real_root(deriv.proj(),ass,poly1,poly2)) {
                    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> common root at " << ran);
                    if (all_relations_weak) return filter_util::result::INCLUSIVE_OPTIONAL;
                    else return filter_util::result::NORMAL_OPTIONAL;
                } else {
                    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> omit root " << ran);
                    return filter_util::result::OMIT;
                }
            }
        });
    }
}

template<typename P>
void delineate_wb(datastructures::SampledDerivation<P>& deriv, const properties::root_ordering_holds& prop) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "delineate(" << prop << ")");

    auto decomposed = ordering_util::decompose(prop.ordering);
    for (const auto& d : decomposed) {
        const auto& poly1 = d.first.first;
        const auto& poly2 = d.first.second;
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "consider pair " << poly1 << " and " << poly2 << "");
        bool all_relations_weak = std::find_if(d.second.begin(), d.second.end(), [](const auto& pair){ return pair.is_strict; }) == d.second.end();
        filter_util::filter_roots(deriv, deriv.proj().res(poly1, poly2), [&](const RAN& ran) {
            if (all_relations_weak) return filter_util::result::INCLUSIVE;
            else return filter_util::result::NORMAL;
        });
    }
}

template<typename P>
bool root_ordering_holds_delineated(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& /*cell*/, const datastructures::IndexedRootOrdering& underlying_ordering, const datastructures::IndexedRootOrdering& ordering) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "ir_ord(" << ordering << ", " << deriv.sample() << ")");
    deriv.insert(properties::cell_connected{ deriv.level() });
    assert(deriv.contains(properties::root_ordering_holds{ underlying_ordering, deriv.level()-1 }));

    auto decomposed = ordering_util::decompose(ordering);
    for (const auto& d : decomposed) {
        const auto& poly1 = d.first.first;
        const auto& poly2 = d.first.second;
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "consider pair " << poly1 << " and " << poly2 << "");
        assert(deriv.contains(properties::poly_pdel{ poly1 }));
        assert(deriv.contains(properties::poly_pdel{ poly2 }));
        filter_util::pseudo_order_invariant(deriv, deriv.proj().res(poly1, poly2), underlying_ordering.polys());
    }
    return true;
}

}