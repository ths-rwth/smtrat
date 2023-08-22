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
                const auto& roots = rel.second.is_cminmax() ? rel.second.cminmax().roots : rel.second.cmaxmin().roots;
                for (const auto& rootsp : roots) {
                    for (const auto& root : rootsp) {
                        add_to_decomposition(result, rel.first.root().poly, root.poly, rel);
                    }
                }
            } else if (!rel.first.is_root() && rel.second.is_root()) {
                const auto& roots = rel.first.is_cminmax() ? rel.first.cminmax().roots : rel.first.cmaxmin().roots;
                for (const auto& rootsp : roots) {
                    for (const auto& root : rootsp) {
                        add_to_decomposition(result, root.poly, rel.second.root().poly, rel);
                    }
                }
            } else {
                const auto& roots1 = rel.first.is_cminmax() ? rel.first.cminmax().roots : rel.first.cmaxmin().roots;
                const auto& roots2 = rel.second.is_cminmax() ? rel.second.cminmax().roots : rel.second.cmaxmin().roots;
                for (const auto& roots1p : roots1) {
                    for (const auto& root1 : roots1p) {
                        for (const auto& roots2p : roots2) {
                            for (const auto& root2 : roots2p) {
                                add_to_decomposition(result, root1.poly, root2.poly, rel);
                            }
                        }
                    }
                }
            }
        }
        return result;
    }
}

namespace compound_util {
    inline std::pair<RAN,std::vector<datastructures::IndexedRoot>> evaluate_min(datastructures::Projections& proj, const Assignment& ass, const std::vector<datastructures::IndexedRoot>& roots) {
        std::vector<datastructures::IndexedRoot> irs;
        RAN value;
        for (const auto& root : roots) {
            auto v = proj.evaluate(ass, root);
            if (irs.empty() || v < value) {
                irs.clear();
                irs.push_back(root);
                value = v;
            } else if (v == value) {
                irs.push_back(root);
            }
        }
        return std::make_pair(value, irs);
    }
    inline std::pair<RAN,std::vector<datastructures::IndexedRoot>> evaluate_max(datastructures::Projections& proj, const Assignment& ass, const std::vector<datastructures::IndexedRoot>& roots) {
        std::vector<datastructures::IndexedRoot> irs;
        RAN value;
        for (const auto& root : roots) {
            auto v = proj.evaluate(ass, root);
            if (irs.empty() || v > value) {
                irs.clear();
                irs.push_back(root);
                value = v;
            } else if (v == value) {
                irs.push_back(root);
            }
        }
        return std::make_pair(value, irs);
    }

    inline std::pair<RAN,std::vector<datastructures::IndexedRoot>> evaluate(datastructures::Projections& proj, const Assignment& ass, const datastructures::CompoundMinMax& bound) {
        std::vector<datastructures::IndexedRoot> irs;
        RAN value;
        for (const auto& roots : bound.roots) {
            auto v = evaluate_max(proj, ass, roots);
            if (irs.empty() || v.first < value) {
                irs.clear();
                irs.insert(irs.end(), v.second.begin(), v.second.end());
                value = v.first;
            } else if (v.first == value) {
                irs.insert(irs.end(), v.second.begin(), v.second.end());
            }
        }
        return std::make_pair(value, irs);
    }

    inline std::pair<RAN,std::vector<datastructures::IndexedRoot>> evaluate(datastructures::Projections& proj, const Assignment& ass, const datastructures::CompoundMaxMin& bound) {
        std::vector<datastructures::IndexedRoot> irs;
        RAN value;
        for (const auto& roots : bound.roots) {
            auto v = evaluate_min(proj, ass, roots);
            if (irs.empty() || v.first > value) {
                irs.clear();
                irs.insert(irs.end(), v.second.begin(), v.second.end());
                value = v.first;
            } else if (v.first == value) {
                irs.insert(irs.end(), v.second.begin(), v.second.end());
            }
        }
        return std::make_pair(value, irs);
    }
}

template<typename P>
void delineate_all_compound(datastructures::SampledDerivation<P>& deriv, const properties::root_ordering_holds& prop, bool enable_weak = true, bool enable_regular = true) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "delineate(" << prop << ", " << enable_weak << ")");

    auto decomposed = ordering_util::decompose(prop.ordering);
    for (const auto& d : decomposed) {
        const auto& poly1 = d.first.first;
        const auto& poly2 = d.first.second;
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "consider pair " << poly1 << " and " << poly2 << "");
        bool all_relations_weak = std::find_if(d.second.begin(), d.second.end(), [](const auto& pair){ return pair.is_strict; }) == d.second.end();
        boost::container::flat_set<datastructures::PolyRef> polys({ poly1, poly2 });
        auto delineable_interval = filter_util::delineable_interval<P>(deriv.proj(), deriv.sample(), polys);
        assert(delineable_interval);
        bool only_regular = std::find_if(d.second.begin(), d.second.end(), [](const auto& pair) { return !(pair.first.is_root() && pair.second.is_root()); }) == d.second.end();
        filter_util::filter_roots(*deriv.delineated(), deriv.proj().res(poly1, poly2), [&](const RAN& ran) {
            if (!enable_regular && only_regular) return filter_util::result::NORMAL;
            Assignment ass = filter_util::projection_root(*deriv.delineated(), ran);
            if (!delineable_interval->contains(ran)) {
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> resultant's root " << ran << " outside of " << delineable_interval);
                if (!enable_regular) return filter_util::result::NORMAL;
                if (filter_util::has_common_real_root(deriv.proj(),ass,poly1,poly2)) {
                    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> common root at " << ran);
                    if (all_relations_weak && enable_weak) return filter_util::result::INCLUSIVE;
                    else return filter_util::result::NORMAL;
                } else {
                    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> no intersection at " << ran);
                    if (all_relations_weak && enable_weak) return filter_util::result::INCLUSIVE_OPTIONAL;
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
                        if (!enable_regular) return filter_util::result::NORMAL;
                        const auto& roots_first = pair.first.root().poly == poly1 ? roots1 : roots2;
                        const auto& roots_second = pair.first.root().poly == poly1 ? roots2 : roots1;
                        auto index_first = pair.first.root().index;
                        auto index_second = pair.second.root().index;
                        assert(index_first <= roots_first.size());
                        assert(index_second <= roots_second.size());
                        if (roots_first[index_first-1] == roots_second[index_second-1]) {
                            SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> relevant intersection at " << ran);
                            if (!pair.is_strict && enable_weak) return filter_util::result::INCLUSIVE;
                            else return filter_util::result::NORMAL;
                        }
                    } else if (pair.first.is_root()) {
                        const auto& roots_first = pair.first.root().poly == poly1 ? roots1 : roots2;
                        auto index_first = pair.first.root().index;
                        assert(index_first <= roots_first.size());
                        auto poly_second = pair.first.root().poly == poly1 ? poly2 : poly1;

                        bool relevant = true; 
                        assert(pair.second.is_cminmax() || pair.second.is_cmaxmin());
                        auto delineable_interval_cb = filter_util::delineable_interval<P>(deriv.proj(), deriv.sample(), pair.second.polys());
                        assert(delineable_interval_cb);
                        if (delineable_interval_cb->contains(ran)) {
                            auto res = pair.second.is_cminmax() ? compound_util::evaluate(deriv.proj(), ass, pair.second.cminmax()) : compound_util::evaluate(deriv.proj(), ass, pair.second.cmaxmin());
                            relevant = false;
                            if (res.first == roots_first[index_first-1]) {
                                relevant = std::find_if(res.second.begin(), res.second.end(), [&](const auto& ir) { return ir.poly == poly_second; }) != res.second.end();
                            }
                        }
                        if (relevant) {
                            SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> relevant intersection at " << ran);
                            if (!pair.is_strict && enable_weak) return filter_util::result::INCLUSIVE;
                            else return filter_util::result::NORMAL;
                        }
                    } else if (pair.second.is_root()) {
                        const auto& roots_second = pair.second.root().poly == poly1 ? roots1 : roots2;
                        auto index_second = pair.second.root().index;
                        assert(index_second <= roots_second.size());
                        auto poly_first = pair.second.root().poly == poly1 ? poly2 : poly1;

                        bool relevant = true; 
                        assert(pair.first.is_cminmax() || pair.first.is_cmaxmin());
                        auto delineable_interval_cb = filter_util::delineable_interval<P>(deriv.proj(), deriv.sample(), pair.first.polys());
                        assert(delineable_interval_cb);
                        if (delineable_interval_cb->contains(ran)) {
                            auto res = pair.first.is_cminmax() ? compound_util::evaluate(deriv.proj(), ass, pair.first.cminmax()) : compound_util::evaluate(deriv.proj(), ass, pair.first.cmaxmin());
                            relevant = false;
                            if (res.first == roots_second[index_second-1]) {
                                relevant = std::find_if(res.second.begin(), res.second.end(), [&](const auto& ir) { return ir.poly == poly_first; }) != res.second.end();
                            }
                        }
                        if (relevant) {
                            SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> relevant intersection at " << ran);
                            if (!pair.is_strict && enable_weak) return filter_util::result::INCLUSIVE;
                            else return filter_util::result::NORMAL;
                        }
                    } else {
                        assert(pair.first.is_cmaxmin() && pair.second.is_cminmax());
                        auto poly_first = (pair.first.has_poly(poly1) && pair.second.has_poly(poly2)) ? poly1 : poly2;
                        auto poly_second = (pair.first.has_poly(poly1) && pair.second.has_poly(poly2)) ? poly2 : poly1;
                        assert(pair.first.has_poly(poly_first) && pair.second.has_poly(poly_second));

                        bool relevant = true;
                        auto cb_polys = pair.first.polys();
                        cb_polys.merge(pair.second.polys());
                        auto delineable_interval_cb = filter_util::delineable_interval<P>(deriv.proj(), deriv.sample(), cb_polys);
                        assert(delineable_interval_cb);
                        if (delineable_interval_cb->contains(ran)) {
                            auto res1 = compound_util::evaluate(deriv.proj(), ass, pair.first.cmaxmin());
                            auto res2 = compound_util::evaluate(deriv.proj(), ass, pair.second.cminmax());
                            relevant = false;
                            if (res1.first == res2.first) {
                                relevant = std::find_if(res1.second.begin(), res1.second.end(), [&](const auto& ir) { return ir.poly == poly_first; }) != res1.second.end() && std::find_if(res2.second.begin(), res2.second.end(), [&](const auto& ir) { return ir.poly == poly_second; }) != res2.second.end();
                            }
                        }
                        if (relevant) {
                            SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> relevant intersection at " << ran);
                            if (!pair.is_strict && enable_weak) return filter_util::result::INCLUSIVE;
                            else return filter_util::result::NORMAL;
                        }
                    }
                }
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> no relevant intersection at " << ran);
                if (all_relations_weak && enable_weak) return filter_util::result::INCLUSIVE_OPTIONAL;
                else return filter_util::result::NORMAL_OPTIONAL;
            }
        });
    }
}

template<typename P>
void delineate_all_compound_piecewiselinear(datastructures::SampledDerivation<P>& deriv, const properties::root_ordering_holds& prop, bool enable_weak = true) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "delineate(" << prop << ", " << enable_weak << ")");

    auto decomposed = ordering_util::decompose(prop.ordering);
    for (const auto& d : decomposed) {
        const auto& poly1 = d.first.first;
        const auto& poly2 = d.first.second;
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "consider pair " << poly1 << " and " << poly2 << "");
        bool all_relations_weak = std::find_if(d.second.begin(), d.second.end(), [](const auto& pair){ return pair.is_strict; }) == d.second.end();
        boost::container::flat_set<datastructures::PolyRef> polys({ poly1, poly2 });
        auto delineable_interval = filter_util::delineable_interval<P>(deriv.proj(), deriv.sample(), polys);
        assert(delineable_interval);
        filter_util::filter_roots(*deriv.delineated(), deriv.proj().res(poly1, poly2), [&](const RAN& ran) {
            Assignment ass = filter_util::projection_root(*deriv.delineated(), ran);
            if (!delineable_interval->contains(ran)) {
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> resultant's root " << ran << " outside of " << delineable_interval);
                return filter_util::result::NORMAL;
            } else {
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> resultant's root " << ran << " in " << delineable_interval);
                for (const auto& pair : d.second) {
                    if (pair.first.is_root() && pair.second.is_root()) {
                        return filter_util::result::NORMAL;
                    } else if (pair.first.is_root()) {
                        assert(pair.second.is_cminmax() || pair.second.is_cmaxmin());
                        auto poly_second = pair.first.root().poly == poly1 ? poly2 : poly1;
                        if ((pair.second.is_cminmax() && pair.second.cminmax().bounds->poly_bound_at(poly_second, ran)) ||
                            (pair.second.is_cmaxmin() && pair.second.cmaxmin().bounds->poly_bound_at(poly_second, ran))) {
                            // we could check whether the correct roots intersect at the given point (i.e. check whether the first indexed root expression is equal to the corresponding bound; but we omit that here...)
                            SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> relevant intersection at " << ran);
                            if (!pair.is_strict && enable_weak) return filter_util::result::INCLUSIVE;
                            else return filter_util::result::NORMAL;
                        }
                    } else if (pair.second.is_root()) {
                        assert(pair.first.is_cminmax() || pair.first.is_cmaxmin());
                        auto poly_first = pair.second.root().poly == poly1 ? poly2 : poly1;
                        if ((pair.first.is_cminmax() && pair.first.cminmax().bounds->poly_bound_at(poly_first, ran)) ||
                            (pair.first.is_cmaxmin() && pair.first.cmaxmin().bounds->poly_bound_at(poly_first, ran))) {
                            SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> relevant intersection at " << ran);
                            if (!pair.is_strict && enable_weak) return filter_util::result::INCLUSIVE;
                            else return filter_util::result::NORMAL;
                        }
                    } else {
                        assert(pair.first.is_cmaxmin() && pair.second.is_cminmax());
                        auto poly_first = (pair.first.has_poly(poly1) && pair.second.has_poly(poly2)) ? poly1 : poly2;
                        auto poly_second = (pair.first.has_poly(poly1) && pair.second.has_poly(poly2)) ? poly2 : poly1;
                        assert(pair.first.has_poly(poly_first) && pair.second.has_poly(poly_second));
                        if (pair.first.cmaxmin().bounds->poly_bound_at(poly_first, ran) && pair.second.cminmax().bounds->poly_bound_at(poly_second, ran)) {
                            SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> relevant intersection at " << ran);
                            if (!pair.is_strict && enable_weak) return filter_util::result::INCLUSIVE;
                            else return filter_util::result::NORMAL;
                        }
                    }
                }
                SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> no relevant intersection at " << ran);
                if (all_relations_weak && enable_weak) return filter_util::result::INCLUSIVE_OPTIONAL;
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
        boost::container::flat_set<datastructures::PolyRef> polys({ poly1, poly2 });
        auto delineable_interval = filter_util::delineable_interval<P>(deriv.proj(), deriv.sample(), polys);
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
        boost::container::flat_set<datastructures::PolyRef> polys({ poly1, poly2 });
        auto delineable_interval = filter_util::delineable_interval<P>(deriv.proj(), deriv.sample(), polys);
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
                boost::container::flat_set<datastructures::PolyRef> polys({ poly1, poly2 });
                delineable_interval = filter_util::delineable_interval<P>(deriv.proj(), deriv.sample(), polys);
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
inline void poly_loc_del(datastructures::SampledDerivation<P>& deriv, const datastructures::PolyRef poly, const boost::container::flat_set<datastructures::PolyRef>& considered_polys) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "poly_loc_del(" << poly << ") wrt " << considered_polys);
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
void poly_ord_inv_base(datastructures::SampledDerivation<P>& deriv, const datastructures::SymbolicInterval& cell, const datastructures::IndexedRootOrdering& /*ordering*/, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "ord_inv_base(" << poly << "), " << poly << " irreducible");
    if (deriv.proj().is_const(poly)) return; 

    if (cell.is_section() && !deriv.proj().is_zero(deriv.sample(), poly)) {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv_base(" << poly << ") <= " << poly << "(" << deriv.sample() << ") != 0 && sgn_inv(" << poly << ")");
        deriv.insert(properties::poly_irreducible_sgn_inv{ poly });
    } else {
        SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> ord_inv_base(" << poly << ") <= del(" << poly << ") && cell_connected(" << poly.level << ")");
        deriv.insert(properties::poly_del{ poly });
        deriv.insert(properties::cell_connected{ poly.level });
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
        assert(deriv.contains(properties::poly_del{ poly1 }));
        assert(deriv.contains(properties::poly_del{ poly2 }));
        poly_loc_del(deriv, deriv.proj().res(poly1, poly2), underlying_ordering.polys());
    }
    return true;
}

template<typename P>
void poly_irreducible_sgn_inv_filtered(datastructures::SampledDerivation<P>& /*deriv*/, const datastructures::SymbolicInterval& /*cell*/, const datastructures::IndexedRootOrdering& /*ordering*/, [[maybe_unused]] datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "sgn_inv(" << poly << "), " << poly << " irreducible");
}

template<typename P>
void poly_irreducible_semi_sgn_inv_filtered(datastructures::SampledDerivation<P>& /*deriv*/, const datastructures::SymbolicInterval& /*cell*/, const datastructures::IndexedRootOrdering& /*ordering*/, [[maybe_unused]] datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "semi_sgn_inv(" << poly << "), " << poly << " irreducible");
}

template<typename P>
void poly_irreducible_nonzero_semi_sgn_inv(datastructures::DelineatedDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "semi_sgn_inv(" << poly << "), " << poly << " irreducible and non-zero");
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> semi_sgn_inv(" << poly << ") <= sgn_inv(" << poly << ")");
    poly_irreducible_nonzero_sgn_inv(deriv, poly);
}

template<typename P>
void poly_irreducible_null_semi_sgn_inv(datastructures::SampledDerivation<P>& deriv, datastructures::PolyRef poly) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "semi_sgn_inv(" << poly << "), " << poly << " irreducible and nullified");
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "-> semi_sgn_inv(" << poly << ") <= sgn_inv(" << poly << ")");
    poly_irreducible_null_sgn_inv(deriv, poly);
}

}