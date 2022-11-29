#pragma once

#include "rules_filter_util.h"

namespace smtrat::cadcells::operators::rules {

namespace ordering_util {
    using Decomposition = boost::container::flat_map<std::pair<datastructures::PolyRef,datastructures::PolyRef>,std::vector<datastructures::IndexedRootRelation>>;

    inline void add_to_decomposition(Decomposition& result, datastructures::PolyRef p1, datastructures::PolyRef p2, const datastructures::IndexedRootRelation& rel) {
        if (p1 != p2) {
            if (p1 < p2) {
                result.try_emplace(std::make_pair(p1, p2)).first->second.push_back(rel);
            } else {
                result.try_emplace(std::make_pair(p2, p1)).first->second.push_back(rel);
            }
        }
    }

    inline auto decompose(const datastructures::IndexedRootOrdering& ordering) {
        Decomposition result;
        for (const auto& rel : ordering.data()) {
            if (rel.first.is_root() && rel.second.is_root()) {
                add_to_decomposition(result, rel.first.root().poly, rel.second.root().poly, rel);
            } else if (rel.first.is_root() && !rel.second.is_root()) {
                const auto& roots = rel.second.is_cmin() ? rel.second.cmin().roots : rel.second.cmax().roots;
                for (const auto& root : roots) {
                    add_to_decomposition(result, rel.first.root().poly, root.poly, rel);
                }
            } else if (!rel.first.is_root() && rel.second.is_root()) {
                const auto& roots = rel.first.is_cmin() ? rel.first.cmin().roots : rel.first.cmax().roots;
                for (const auto& root : roots) {
                    add_to_decomposition(result, root.poly, rel.second.root().poly, rel);
                }
            } else {
                assert(rel.first.is_cmax() && rel.second.is_cmin());
                for (const auto& root1 : rel.first.cmax().roots) {
                    for (const auto& root2 : rel.second.cmin().roots) {
                        add_to_decomposition(result, root1.poly, root2.poly, rel);
                    }
                }
            }
        }
        return result;
    }
}

template<typename P>
void delineate_all_compound(datastructures::SampledDerivation<P>& deriv, const properties::root_ordering_holds& prop) {
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
                    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> no intersection at " << ran);
                    if (all_relations_weak) return filter_util::result::INCLUSIVE_OPTIONAL;
                    else return filter_util::result::NORMAL_OPTIONAL;
                }
            } else {
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> resultant's root " << ran << " in " << delineable_interval);
                assert(!deriv.proj().is_nullified(ass,poly1));
                assert(!deriv.proj().is_nullified(ass,poly2));
                auto roots1 = deriv.proj().real_roots(ass,poly1);
                auto roots2 = deriv.proj().real_roots(ass,poly2);
                for (const auto& pair : d.second) {
                    if (pair.first.is_root() && pair.second.is_root()) {
                        const auto& roots_first = pair.first.root().poly == poly1 ? roots1 : roots2;
                        const auto& roots_second = pair.first.root().poly == poly1 ? roots2 : roots1;
                        auto index_first = pair.first.root().index;
                        auto index_second = pair.second.root().index;
                        assert(index_first <= roots_first.size());
                        assert(index_second <= roots_second.size());
                        if (roots_first[index_first-1] == roots_second[index_second-1]) {
                            SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> relevant intersection at " << ran);
                            if (!pair.is_strict) return filter_util::result::INCLUSIVE;
                            else return filter_util::result::NORMAL;
                        }
                    } else if (pair.first.is_root()) {
                        const auto& roots_first = pair.first.root().poly == poly1 ? roots1 : roots2;
                        const auto& roots_second = pair.first.root().poly == poly1 ? roots2 : roots1;
                        auto index_first = pair.first.root().index;
                        auto index_second = pair.second.poly_root(pair.first.root().poly == poly1 ? poly2 : poly1)->index;
                        assert(index_first <= roots_first.size());
                        assert(index_second <= roots_second.size());
                        if (roots_first[index_first-1] == roots_second[index_second-1]) {
                            bool relevant = true; 
                            if (pair.second.is_cmin()) {
                                auto delineable_interval_cb = filter_util::delineable_interval<P>(deriv.proj(), deriv.sample(), std::vector<datastructures::PolyRef>( pair.second.polys().begin(), pair.second.polys().end() ));
                                assert(delineable_interval_cb);
                                if (delineable_interval_cb->contains(ran)) {
                                    for (const auto& root : pair.second.roots()) {
                                        if (deriv.proj().evaluate(ass, root) < roots_second[index_second-1]) {
                                            relevant = false;
                                            break;
                                        }
                                    }
                                }
                            }
                            if (relevant) {
                                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> relevant intersection at " << ran);
                                if (!pair.is_strict) return filter_util::result::INCLUSIVE;
                                else return filter_util::result::NORMAL;
                            }
                        } 
                    } else if (pair.second.is_root()) {
                        const auto& roots_first = pair.second.root().poly == poly2 ? roots1 : roots2;
                        const auto& roots_second = pair.second.root().poly == poly2 ? roots2 : roots1;
                        auto index_first = pair.first.poly_root(pair.second.root().poly == poly2 ? poly1 : poly2)->index; 
                        auto index_second = pair.second.root().index;
                        assert(index_first <= roots_first.size());
                        assert(index_second <= roots_second.size());
                        if (roots_first[index_first-1] == roots_second[index_second-1]) {
                            bool relevant = true; 
                            if (pair.second.is_cmax()) {
                                auto delineable_interval_cb = filter_util::delineable_interval<P>(deriv.proj(), deriv.sample(), std::vector<datastructures::PolyRef>( pair.second.polys().begin(), pair.second.polys().end() ));
                                assert(delineable_interval_cb);
                                if (delineable_interval_cb->contains(ran)) {
                                    for (const auto& root : pair.first.roots()) {
                                        if (deriv.proj().evaluate(ass, root) > roots_first[index_first-1]) {
                                            relevant = false;
                                            break;
                                        }
                                    }
                                }
                            }
                            if (relevant) {
                                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> relevant intersection at " << ran);
                                if (!pair.is_strict) return filter_util::result::INCLUSIVE;
                                else return filter_util::result::NORMAL;
                            }
                        } 
                    } else {
                        assert(pair.second.is_cmax() && pair.second.is_cmin());
                        const auto& roots_first = pair.first.has_poly(poly1) ? roots1 : roots2;
                        const auto& roots_second = pair.first.has_poly(poly1) ? roots2 : roots1;
                        auto index_first = pair.first.poly_root(pair.first.has_poly(poly1) ? poly1 : poly2)->index; 
                        auto index_second = pair.second.poly_root(pair.first.has_poly(poly1) ? poly2 : poly1)->index; 
                        assert(index_first <= roots_first.size());
                        assert(index_second <= roots_second.size());
                        if (roots_first[index_first-1] == roots_second[index_second-1]) {
                            SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> relevant intersection at " << ran);
                            if (!pair.is_strict) return filter_util::result::INCLUSIVE;
                            else return filter_util::result::NORMAL;
                        }
                    }
                }
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> no relevant intersection at " << ran);
                if (all_relations_weak) return filter_util::result::INCLUSIVE_OPTIONAL;
                else return filter_util::result::NORMAL_OPTIONAL;
            }
        });
    }
}

template<typename P>
void delineate_all(datastructures::SampledDerivation<P>& deriv, const properties::root_ordering_holds& prop) {
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
                    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> no intersection at " << ran);
                    if (all_relations_weak) return filter_util::result::INCLUSIVE_OPTIONAL;
                    else return filter_util::result::NORMAL_OPTIONAL;
                }
            } else {
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> resultant's root " << ran << " in " << delineable_interval);
                assert(!deriv.proj().is_nullified(ass,poly1));
                assert(!deriv.proj().is_nullified(ass,poly2));
                auto roots1 = deriv.proj().real_roots(ass,poly1);
                auto roots2 = deriv.proj().real_roots(ass,poly2);
                for (const auto& pair : d.second) {
                    assert(pair.first.is_root() && pair.second.is_root());
                    auto index1 = pair.first.root().poly == poly1 ? pair.first.root().index : pair.second.root().index;
                    auto index2 = pair.first.root().poly == poly1 ? pair.second.root().index : pair.first.root().index;
                    assert(index1 <= roots1.size());
                    assert(index2 <= roots2.size());
                    if (roots1[index1-1] == roots2[index2-1]) {
                        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> relevant intersection at " << ran);
                        // if (all_relations_weak) return filter_util::result::INCLUSIVE;
                        // else return filter_util::result::NORMAL;
                        if (!pair.is_strict) return filter_util::result::INCLUSIVE;
                        else return filter_util::result::NORMAL;
                    }
                }
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> no relevant intersection at " << ran);
                if (all_relations_weak) return filter_util::result::INCLUSIVE_OPTIONAL;
                else return filter_util::result::NORMAL_OPTIONAL;
            }
        });
    }
}

template<typename P>
void delineate_samples(datastructures::SampledDerivation<P>& deriv, const properties::root_ordering_holds& prop) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "delineate(" << prop << ")");

    auto decomposed = ordering_util::decompose(prop.ordering);
    for (const auto& d : decomposed) {
        const auto& poly1 = d.first.first;
        const auto& poly2 = d.first.second;
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "consider pair " << poly1 << " and " << poly2 << "");
        auto delineable_interval = filter_util::delineable_interval<P>(deriv.proj(), deriv.sample(), std::vector<datastructures::PolyRef>({ poly1, poly2 }));
        assert(delineable_interval);
        filter_util::filter_roots(*deriv.delineated(), deriv.proj().res(poly1, poly2), [&](const RAN& ran) {
            Assignment ass = filter_util::projection_root(*deriv.delineated(), ran);
            if (!delineable_interval->contains(ran)) {
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> resultant's root " << ran << " outside of " << delineable_interval);
                if (filter_util::has_common_real_root(deriv.proj(),ass,poly1,poly2)) {
                    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> common root at " << ran);
                    return filter_util::result::NORMAL;
                } else {
                    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> no intersection at " << ran);
                    return filter_util::result::NORMAL_OPTIONAL;
                }
            } else {
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> resultant's root " << ran << " in " << delineable_interval);
                assert(!deriv.proj().is_nullified(ass,poly1));
                assert(!deriv.proj().is_nullified(ass,poly2));
                auto roots1 = deriv.proj().real_roots(ass,poly1);
                auto roots2 = deriv.proj().real_roots(ass,poly2);
                for (const auto& pair : d.second) {
                    assert(pair.first.is_root() && pair.second.is_root());
                    auto index1 = pair.first.root().poly == poly1 ? pair.first.root().index : pair.second.root().index;
                    auto index2 = pair.first.root().poly == poly1 ? pair.second.root().index : pair.first.root().index;
                    assert(index1 <= roots1.size());
                    assert(index2 <= roots2.size());
                    if (roots1[index1-1] == roots2[index2-1]) {
                        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> relevant intersection at " << ran);
                        return filter_util::result::NORMAL;
                    }
                }
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> no relevant intersection at " << ran);
                return filter_util::result::NORMAL_OPTIONAL;
            }
        });
    }
}

template<typename P>
void delineate_all_selective(datastructures::SampledDerivation<P>& deriv, const properties::root_ordering_holds& prop) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "delineate(" << prop << ")");

    bool algebraic = std::find_if(deriv.underlying_sample().begin(), deriv.underlying_sample().end(), [](const auto& m) { return !m.second.is_numeric(); }) != deriv.underlying_sample().end();

    auto decomposed = ordering_util::decompose(prop.ordering);
    for (const auto& d : decomposed) {
        const auto& poly1 = d.first.first;
        const auto& poly2 = d.first.second;
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "consider pair " << poly1 << " and " << poly2 << "");
        bool all_relations_weak = std::find_if(d.second.begin(), d.second.end(), [](const auto& pair){ return pair.is_strict; }) == d.second.end();
        std::optional<carl::Interval<RAN>> delineable_interval;
        filter_util::filter_roots(*deriv.delineated(), deriv.proj().res(poly1, poly2), [&](const RAN& ran) {
            if (algebraic || !ran.is_numeric()) {
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> sample is algebraic, adding " << ran);
                // return filter_util::result::NORMAL;
                if (all_relations_weak) return filter_util::result::INCLUSIVE;
                else return filter_util::result::NORMAL;
            }
            if (!delineable_interval) {
                delineable_interval = filter_util::delineable_interval<P>(deriv.proj(), deriv.sample(), std::vector<datastructures::PolyRef>({ poly1, poly2 }));
                assert(delineable_interval);
            }
            Assignment ass = filter_util::projection_root(*deriv.delineated(), ran);
            if (!delineable_interval->contains(ran)) {
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> resultant's root " << ran << " outside of " << delineable_interval);
                if (filter_util::has_common_real_root(deriv.proj(),ass,poly1,poly2)) { // TODO disable check?
                    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> common root at " << ran);
                    // return filter_util::result::NORMAL;
                    if (all_relations_weak) return filter_util::result::INCLUSIVE;
                    else return filter_util::result::NORMAL;
                } else {
                    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> no intersection at " << ran);
                    // return filter_util::result::NORMAL_OPTIONAL;
                    if (all_relations_weak) return filter_util::result::INCLUSIVE_OPTIONAL;
                    else return filter_util::result::NORMAL_OPTIONAL;
                }
            } else {
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> resultant's root " << ran << " in " << delineable_interval);
                assert(!deriv.proj().is_nullified(ass,poly1));
                assert(!deriv.proj().is_nullified(ass,poly2));
                auto roots1 = deriv.proj().real_roots(ass,poly1);
                auto roots2 = deriv.proj().real_roots(ass,poly2);
                for (const auto& pair : d.second) {
                    assert(pair.first.is_root() && pair.second.is_root());
                    auto index1 = pair.first.root().poly == poly1 ? pair.first.root().index : pair.second.root().index;
                    auto index2 = pair.first.root().poly == poly1 ? pair.second.root().index : pair.first.root().index;
                    assert(index1 <= roots1.size());
                    assert(index2 <= roots2.size());
                    if (roots1[index1-1] == roots2[index2-1]) {
                        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> relevant intersection at " << ran);
                        // return filter_util::result::NORMAL;
                        if (!pair.is_strict) return filter_util::result::INCLUSIVE;
                        else return filter_util::result::NORMAL;
                    }
                }
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> no relevant intersection at " << ran);
                // return filter_util::result::NORMAL_OPTIONAL;
                if (all_relations_weak) return filter_util::result::INCLUSIVE_OPTIONAL;
                else return filter_util::result::NORMAL_OPTIONAL;
            }
        });
    }
}

template<typename P>
void delineate_bounds(datastructures::SampledDerivation<P>& deriv, const properties::root_ordering_holds& prop) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "delineate(" << prop << ")");

    auto decomposed = ordering_util::decompose(prop.ordering);
    for (const auto& d : decomposed) {
        const auto& poly1 = d.first.first;
        const auto& poly2 = d.first.second;
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "consider pair " << poly1 << " and " << poly2 << "");
        bool all_relations_weak = std::find_if(d.second.begin(), d.second.end(), [](const auto& pair){ return pair.is_strict; }) == d.second.end();
        filter_util::filter_roots(*deriv.delineated(), deriv.proj().res(poly1, poly2), [&](const RAN&) {
            if (all_relations_weak) return filter_util::result::INCLUSIVE;
            else return filter_util::result::NORMAL;
        });
    }
}

template<typename P>
void delineate_noop(datastructures::SampledDerivation<P>& deriv, const properties::root_ordering_holds& prop) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "delineate(" << prop << ")");

    auto decomposed = ordering_util::decompose(prop.ordering);
    for (const auto& d : decomposed) {
        const auto& poly1 = d.first.first;
        const auto& poly2 = d.first.second;
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "consider pair " << poly1 << " and " << poly2 << "");
        filter_util::filter_roots(*deriv.delineated(), deriv.proj().res(poly1, poly2), [&](const RAN&) {
            return filter_util::result::NORMAL;
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