#pragma once

#include "../CADCellsStatistics.h"

namespace smtrat::cadcells::representation::util {

inline bool compare_simplest(datastructures::Projections& proj, datastructures::PolyRef p1, datastructures::PolyRef p2) {
    return proj.degree(p1) < proj.degree(p2);
    //return proj.max_degree(p1) < proj.max_degree(p2);
}

inline bool max_degree(datastructures::Projections& proj, datastructures::RootFunction rf) {
    if (rf.is_root()) {
        return proj.degree(rf.root().poly);
    } else {
        std::size_t deg = 0;
        for (const auto& p : rf.polys()) {
            auto d = proj.degree(p);
            if (deg < d) deg = d;
        }
        return deg;
    }
}

inline bool compare_simplest(datastructures::Projections& proj, datastructures::RootFunction rf1, datastructures::RootFunction rf2) {
    return max_degree(proj, rf1) < max_degree(proj, rf2);
}

inline std::optional<datastructures::IndexedRoot> simplest_bound(datastructures::Projections& proj, const std::vector<datastructures::TaggedIndexedRoot>& bounds, datastructures::PolyRef origin_filter) {
    assert(!bounds.empty());
    std::optional<datastructures::IndexedRoot> simplest;
    for (auto iter = bounds.begin(); iter != bounds.end(); iter++) {
        if (!iter->origin || *iter->origin != origin_filter) continue;
        if (!simplest || compare_simplest(proj,iter->root.poly,simplest->poly)) {
            simplest = iter->root;
        }
    }
    return simplest;
}

inline datastructures::IndexedRoot simplest_bound(datastructures::Projections& proj, const std::vector<datastructures::TaggedIndexedRoot>& bounds, bool enable_weak = false) {
    assert(!bounds.empty());
    auto simplest = bounds.begin();
    for (auto iter = bounds.begin(); iter != bounds.end(); iter++) {
        if (enable_weak && iter->is_inclusive != simplest->is_inclusive) {
            if (simplest->is_inclusive) {
                simplest = iter;
            }
        } else if (compare_simplest(proj,iter->root.poly,simplest->root.poly)) {
            simplest = iter;
        }
    }
    return simplest->root;
}

inline datastructures::SymbolicInterval compute_simplest_cell([[maybe_unused]] std::size_t level, datastructures::Projections& proj, const datastructures::DelineationInterval& del, bool enable_weak = false) {
    if (del.is_section()) {
        SMTRAT_STATISTICS_CALL(statistics().section_common_zeros(level, del.lower()->second.size()));
        SMTRAT_STATISTICS_CALL(statistics().got_bound(level, datastructures::SymbolicInterval(util::simplest_bound(proj, del.lower()->second))));
        return datastructures::SymbolicInterval(util::simplest_bound(proj, del.lower()->second));
    } else {
        datastructures::Bound lower = datastructures::Bound::infty();
        datastructures::Bound upper = datastructures::Bound::infty();
        if (!del.lower_unbounded()) {
            assert(enable_weak || del.lower_strict());
            if (del.lower_strict()) {
                lower = datastructures::Bound::strict(util::simplest_bound(proj, del.lower()->second, enable_weak));
            } else {
                lower = datastructures::Bound::weak(util::simplest_bound(proj, del.lower()->second, enable_weak));
            }
        }
        if (!del.upper_unbounded()) {
            assert(enable_weak || del.upper_strict());
            if (del.upper_strict()) {
                upper = datastructures::Bound::strict(util::simplest_bound(proj, del.upper()->second, enable_weak));
            } else {
                upper = datastructures::Bound::weak(util::simplest_bound(proj, del.upper()->second, enable_weak));
            }
        }
        SMTRAT_STATISTICS_CALL(statistics().got_bound(level, datastructures::SymbolicInterval(lower, upper)));
        return datastructures::SymbolicInterval(lower, upper);
    }
}

inline void simplest_biggest_cell_ordering(datastructures::Projections& /*proj*/, const datastructures::Delineation& delin, const datastructures::DelineationInterval& delin_interval, const datastructures::SymbolicInterval& interval, datastructures::IndexedRootOrdering& ordering, bool enable_weak = false) {
    // assumes that interval is the simplest cell

    if (delin.roots().empty()) return;
    
    if (!delin_interval.lower_unbounded()) {
        auto it = delin_interval.lower();
        bool at_lower = true;
        while(true) {
            for (const auto& ir : it->second) {
                if (ir.root != interval.lower().value()) {
                    if (enable_weak && (interval.lower().is_strict() || (ir.is_inclusive))) {
                        ordering.add_leq(ir.root, interval.lower().value());
                    } else {
                        if (at_lower) {
                            ordering.add_eq(ir.root, interval.lower().value());
                        } else {
                            ordering.add_less(ir.root, interval.lower().value());
                        }
                    }
                } 
            }
            at_lower = false;
            if (it != delin.roots().begin()) it--;
            else break;
        }
    }
    if (!delin_interval.upper_unbounded()) {
        auto it = delin_interval.upper();
        bool at_upper = true;
        while(it != delin.roots().end()) {
            for (const auto& ir : it->second) {
                if (ir.root != interval.upper().value()) {
                    if (enable_weak && (interval.upper().is_strict() || (ir.is_inclusive))) {
                        ordering.add_leq(interval.upper().value(), ir.root);
                    } else {
                        if (at_upper) {
                            ordering.add_eq(interval.upper().value(), ir.root);
                        } else {
                            ordering.add_less(interval.upper().value(), ir.root);
                        }
                    }
                }
            }
            at_upper = false;
            it++;
        }
    }
}

inline void simplest_chain_ordering(datastructures::Projections& proj, const datastructures::Delineation& delin, datastructures::IndexedRootOrdering& ordering, bool enable_weak = false) {
    assert(!enable_weak); // not supported

    if (delin.roots().empty()) return ;

    auto it = delin.roots().begin();
    auto barrier = simplest_bound(proj, it->second);
    while(it != delin.roots().end()) {
        auto simplest = simplest_bound(proj, it->second);
        if (barrier != simplest) {
            ordering.add_less(barrier, simplest);
        }
        for (const auto& ir : it->second) {
            if (ir.root != simplest) {
                ordering.add_eq(simplest, ir.root);
            }
        }
        barrier = simplest;
        it++;
    }
}

inline void simplest_ldb_ordering(datastructures::Projections& proj, const datastructures::Delineation& delin, const datastructures::DelineationInterval& delin_interval, const datastructures::SymbolicInterval& interval, datastructures::IndexedRootOrdering& ordering, boost::container::flat_set<datastructures::PolyRef>& equational, bool enable_weak, bool use_global_cache) {
    // assumes that interval is the simplest cell

    auto has_resultant = [&proj,&ordering,&use_global_cache](datastructures::PolyRef p, datastructures::PolyRef q) -> bool {
        assert(p.level == q.level);
        if (p.id == q.id) return true;
        if (use_global_cache && proj.know_res(p,q)) return true;
        return ordering.has_pair(p,q);
    };

    const bool section = delin_interval.is_section();
    while(section) {
        auto old_size = equational.size();

        auto it = delin_interval.lower();
        while(true) {
            for (auto ir = it->second.begin(); ir != it->second.end(); ir++) {
                if (ir->root.poly == interval.section_defining().poly) continue;
                if (equational.contains(ir->root.poly)) continue;
                if (!util::compare_simplest(proj,ir->root,interval.section_defining())) {
                    equational.insert(ir->root.poly);
                }
            }
            if (it != delin.roots().begin()) it--;
            else break;
        }

        it = delin_interval.upper();
        while(it != delin.roots().end()) {
            for (auto ir = it->second.begin(); ir != it->second.end(); ir++) {
                if (ir->root.poly == interval.section_defining().poly) continue;
                if (equational.contains(ir->root.poly)) continue;
                if (!util::compare_simplest(proj,ir->root,interval.section_defining())) {
                    equational.insert(ir->root.poly);
                }
            }
            it++;
        }

        if (old_size == equational.size()) {
            break;
        }
    }

    if (!delin_interval.lower_unbounded()) {
        std::vector<datastructures::RootFunction> reached;
        auto it = delin_interval.lower();
        auto barrier = interval.lower().value();
        bool barrier_incl = interval.lower().is_weak();
        reached.push_back(barrier);
        while(true) {
            auto old_barrier = barrier;
            bool old_barrier_incl = barrier_incl;
            for (auto ir = it->second.begin(); ir != it->second.end(); ir++) {
                if (section && equational.contains(ir->root.poly)) continue;
                if (util::compare_simplest(proj,ir->root,barrier) || barrier == ir->root) {
                    if (barrier == ir->root) {
                        barrier_incl = ir->is_inclusive && barrier_incl;
                    }
                    barrier = ir->root;
                }
            }
            assert(it != delin_interval.lower() || barrier == interval.lower().value());
            if (barrier != old_barrier) {
                bool rchd = false;
                for (const auto& r : reached) {
                    if(barrier.is_root() && r.is_root() && has_resultant(barrier.root().poly,r.root().poly)) {
                        if (enable_weak && interval.upper().is_strict()) {
                            ordering.add_leq(barrier, r);
                        } else {
                            ordering.add_less(barrier, r);
                        }
                        rchd = true;
                    }
                }
                if (!rchd) {
                    if (enable_weak && (interval.lower().is_strict() || barrier_incl || !old_barrier_incl)) {
                        ordering.add_leq(barrier, old_barrier);
                    } else {
                        ordering.add_less(barrier, old_barrier);
                    }
                }
                reached.push_back(barrier);
            }
            for (const auto& ir : it->second) {
                if (section && equational.contains(ir.root.poly)) continue;
                if (ir.root != barrier) {
                    bool rchd = false;
                    for (const auto& r : reached) {
                        if(r.is_root() && has_resultant(ir.root.poly,r.root().poly)) {
                            if (enable_weak && interval.upper().is_strict()) {
                                ordering.add_leq(ir.root, r);
                            } else {
                                ordering.add_less(ir.root, r);
                            }
                            rchd = true;
                        }
                    }
                    if (!rchd) {
                        if (enable_weak && (interval.lower().is_strict() || ir.is_inclusive || !barrier_incl)) {
                            ordering.add_leq(ir.root, barrier);
                        } else {
                            ordering.add_less(ir.root, barrier);
                        }
                    }
                    reached.push_back(ir.root);
                } 
            }
            if (it != delin.roots().begin()) it--;
            else break;
        }
    }

    if (!delin_interval.upper_unbounded()) {
        std::vector<datastructures::RootFunction> reached;
        auto it = delin_interval.upper();
        auto barrier = interval.upper().value();
        bool barrier_incl = interval.upper().is_weak();
        reached.push_back(barrier);
        while(it != delin.roots().end()) {
            auto old_barrier = barrier;
            bool old_barrier_incl = barrier_incl;
            for (auto ir = it->second.begin(); ir != it->second.end(); ir++) {
                if (section && equational.contains(ir->root.poly)) continue;
                if (util::compare_simplest(proj,ir->root,barrier) || barrier == ir->root) {
                    if (barrier == ir->root) {
                        barrier_incl = ir->is_inclusive && barrier_incl;
                    }
                    barrier = ir->root;
                }
            }
            assert(it != delin_interval.upper() || barrier == interval.upper().value());
            if (barrier != old_barrier) {
                bool rchd = false;
                for (const auto& r : reached) {
                    if(barrier.is_root() && r.is_root() && has_resultant(barrier.root().poly,r.root().poly)) {
                        if (enable_weak && interval.upper().is_strict()) {
                            ordering.add_leq(r, barrier);
                        } else {
                            ordering.add_less(r, barrier);
                        }
                        rchd = true;
                    }
                }
                if (!rchd) {
                    if (enable_weak && (interval.upper().is_strict() || barrier_incl || !old_barrier_incl)) {
                        ordering.add_leq(old_barrier, barrier);
                    } else {
                        ordering.add_less(old_barrier, barrier);
                    }
                }
                reached.push_back(barrier);
            }
            for (const auto& ir : it->second) {
                if (section && equational.contains(ir.root.poly)) continue;
                if (ir.root != barrier) {
                    bool rchd = false;
                    for (const auto& r : reached) {
                        if(r.is_root() && has_resultant(ir.root.poly,r.root().poly)) {
                            if (enable_weak && interval.upper().is_strict()) {
                                ordering.add_leq(r, ir.root);
                            } else {
                                ordering.add_less(r, ir.root);
                            }
                            rchd = true;
                        }
                    }
                    if (!rchd) {
                        if (enable_weak && (interval.upper().is_strict() || ir.is_inclusive || !barrier_incl)) {
                            ordering.add_leq(barrier, ir.root);
                        } else {
                            ordering.add_less(barrier, ir.root);
                        }
                    }
                    reached.push_back(ir.root);
                } 
            }
            it++;
        }
    }
}

/// Polynomial decomposition

struct PolyDelineation {
    boost::container::flat_set<std::size_t> delineated_roots;
    std::size_t critical_lower_root = 0;
    std::size_t critical_upper_root = 0;
};

struct PolyDelineations {
    boost::container::flat_map<datastructures::PolyRef,PolyDelineation> data;
    inline auto& get(const datastructures::PolyRef& poly) {
        if (data.find(poly) == data.end()) {
            data.emplace(poly, PolyDelineation());
        }
        return data[poly];
    }
};

inline void decompose(datastructures::Delineation& delin, const datastructures::DelineationInterval& delin_interval, PolyDelineations& poly_delins) {
    if (!delin_interval.lower_unbounded()) {
        boost::container::flat_set<datastructures::PolyRef> seen;
        auto it = delin_interval.lower();
        while(true) {
            for (const auto& ir : it->second) {
                assert(!ir.origin && !ir.is_optional);
                poly_delins.get(ir.root.poly).delineated_roots.insert(ir.root.index);
                if (!seen.contains(ir.root.poly)) {
                    poly_delins.get(ir.root.poly).critical_lower_root = ir.root.index;
                    seen.insert(ir.root.poly);
                } else {
                    delin.remove_root(it->first,ir);
                }
            }
            if (it != delin.roots().begin()) it--;
            else break;
        }
    }
    if (!delin_interval.upper_unbounded()) {
        boost::container::flat_set<datastructures::PolyRef> seen;
        auto it = delin_interval.upper();
        while(it != delin.roots().end()) {
            for (const auto& ir : it->second) {
                assert(!ir.origin && !ir.is_optional);
                poly_delins.get(ir.root.poly).delineated_roots.insert(ir.root.index);
                if (!seen.contains(ir.root.poly)) {
                    poly_delins.get(ir.root.poly).critical_upper_root = ir.root.index;
                    seen.insert(ir.root.poly);
                } else {
                    delin.remove_root(it->first,ir);
                }
            }
            it++;
        }
    }
}

inline void chain_ordering(const datastructures::PolyRef poly, const PolyDelineation& poly_delin, datastructures::IndexedRootOrdering& ordering) {
    //assert(poly_delin.critical_lower_root == 0 && poly_delin.critical_upper_root == 0);
    for (auto it = poly_delin.delineated_roots.begin(); it != poly_delin.delineated_roots.end() && it != std::prev(poly_delin.delineated_roots.end()); it++) {
        ordering.add_less(datastructures::IndexedRoot(poly,*it),datastructures::IndexedRoot(poly,*(it+1)));
    }
}

inline void biggest_cell_ordering(const datastructures::PolyRef poly, const PolyDelineation& poly_delin, datastructures::IndexedRootOrdering& ordering) {
    if (poly_delin.critical_lower_root != 0) {
            for (auto it = poly_delin.delineated_roots.begin(); *it != poly_delin.critical_lower_root; it++) {
            ordering.add_less(datastructures::IndexedRoot(poly,*it),datastructures::IndexedRoot(poly,poly_delin.critical_lower_root));
        }
    }
    if (poly_delin.critical_upper_root != 0) {
            for (auto it = poly_delin.delineated_roots.rbegin(); *it != poly_delin.critical_upper_root; it++) {
            ordering.add_less(datastructures::IndexedRoot(poly,poly_delin.critical_upper_root), datastructures::IndexedRoot(poly,*it));
        }
    }
}

/// Local delineability

inline auto get_local_del_polys(const datastructures::Delineation& delin) {
    boost::container::flat_set<datastructures::PolyRef> polys;
    for (auto it = delin.roots().begin(); it != delin.roots().end(); it++) {
        for (const auto& t_root : it->second) {
            if (t_root.origin) {
                polys.insert(*t_root.origin);
            }
        }
    }
    return polys;
}

inline bool local_del_poly_independent(const datastructures::Delineation& delin, const datastructures::PolyRef& poly) {
    for (auto it = delin.roots().begin(); it != delin.roots().end(); it++) {
        for (const auto& t_root : it->second) {
            if (t_root.origin && *t_root.origin == poly) {
                if (!t_root.is_optional) {
                    return false;
                }
            }
        }
    }
    return true;
}

inline void local_del_ordering(datastructures::Projections& proj, const datastructures::PolyRef poly, const cadcells::Assignment& ass, const cadcells::RAN& sample, datastructures::Delineation& delin, const datastructures::SymbolicInterval& interval, datastructures::IndexedRootOrdering& ordering) {    
    // Choose l and l' - the range of optional roots that may be inside the cell.
    // We choose it as large as possible.
    std::optional<datastructures::RootMap::const_iterator> ri_begin;
    std::optional<datastructures::RootMap::const_iterator> ri_end;
    for (auto it = delin.roots().begin(); it != delin.roots().end(); it++) {
        bool only_optional_roots = true;
        bool has_root = false;
        for (const auto& t_root : it->second) {
            if (t_root.origin && *t_root.origin == poly) {
                has_root = true;
                if (!t_root.is_optional) {
                    only_optional_roots = false;
                    break;
                }
            }
        }
        if (has_root) {
            if (only_optional_roots) {
                if (!ri_begin) ri_begin = it;
                ri_end = std::next(it);
            } else if (it->first > sample) {
                break;
            } else {
                ri_begin = std::nullopt;
                ri_end = std::nullopt;
            }
            
        }
    }
    assert((bool)ri_begin == (bool)ri_end);

    // Maybe-inside-roots: Add pairs to the ordering, remove them from the delineation.
    datastructures::IndexedRoot ri_first;
    datastructures::IndexedRoot ri_last;
    if (ri_begin && ri_end) {
        // assert(((*ri_begin) == delin.roots().begin() || std::prev(*ri_begin)->first < sample) && ((*ri_end) == delin.roots().end() || sample < (*ri_end)->first)); // this assertion is faulty
        datastructures::IndexedRoot prev;
        for (auto it = *ri_begin; it != *ri_end; it++) {
            if (it->second.empty()) continue;
            auto simplest = simplest_bound(proj, it->second, poly);
            if (simplest) {
                if (ri_first == datastructures::IndexedRoot()) ri_first = *simplest;
                ri_last = *simplest;
                for (const auto& t_root : it->second) {
                    assert(!(t_root.origin && *t_root.origin == poly) || t_root.is_optional);
                    if (*t_root.origin == poly && t_root.root != *simplest) {
                        ordering.add_eq(*simplest, t_root.root);
                    }
                }
                if (prev != datastructures::IndexedRoot()) {
                    ordering.add_less(prev, *simplest);
                }
                prev = *simplest;
                delin.remove_roots_with_origin(it->first, poly);
            }
        }
    }

    // Connect ri_first
    bool p_at_lower = false; 
    if (ri_first != datastructures::IndexedRoot()) {
        assert(*ri_begin != *ri_end);
        bool use_interval_bound = false;
        if (!interval.lower().is_infty()) {
            auto lower = proj.evaluate(ass, interval.lower().value()).first;
            if (lower <= (*ri_begin)->first) {
                if (!interval.lower().value().is_root()) {
                    use_interval_bound = false;
                } else { // if there is a root with higher degree below, we take the interval bound
                    auto bound_deg = proj.total_degree(interval.lower().value().root().poly);
                    if (*ri_begin != delin.roots().begin()) {
                        auto it = std::prev(*ri_begin);
                        while (!use_interval_bound) {
                            for (const auto& t_root : it->second) {
                                if (*t_root.origin == poly) {
                                    if (proj.total_degree(t_root.root.poly) > bound_deg) {
                                        use_interval_bound = true;
                                        break;
                                    }
                                }
                            }
                            if (it == delin.roots().begin()) break;
                            it--;
                        }
                    }
                }
            } else { // some roots are outside, thus we cannot use the interval bound
                use_interval_bound = false;
            }
        }
        if (!use_interval_bound) { // Connect ri_first with all roots below
            if (*ri_begin != delin.roots().begin()) {
                auto it = std::prev(*ri_begin);
                while (true) {
                    for (const auto& t_root : it->second) {
                        if (*t_root.origin == poly) {
                            ordering.add_less(t_root.root, ri_first);
                        }
                    }
                    if (it == delin.roots().begin()) break;
                    it--;
                }
            }
        } else { // Connect ri_first with interval.lower().value()
            if ((*ri_begin)->first == proj.evaluate(ass, interval.lower().value()).first) {
                ordering.add_eq(interval.lower().value(), ri_first);
                p_at_lower = true;
            } else {
                ordering.add_less(interval.lower().value(), ri_first);
            }
        }
    }

    // Connect for ri_last
    bool p_at_upper = false; 
    if (ri_last != datastructures::IndexedRoot()) {
        assert(*ri_begin != *ri_end);
        bool use_interval_bound = false;
        if (!interval.upper().is_infty()) {
            auto upper = proj.evaluate(ass, interval.upper().value()).first;
            if (upper >= std::prev(*ri_end)->first) {
                if (!interval.upper().value().is_root()) {
                    use_interval_bound = false;
                } else { // if there is a root with higher degree below, we take the interval bound
                    auto bound_deg = proj.total_degree(interval.upper().value().root().poly);
                    for (auto it = *ri_end; it != delin.roots().end() && use_interval_bound; it++) {
                        for (const auto& t_root : it->second) {
                            if (*t_root.origin == poly) {
                                if (proj.total_degree(t_root.root.poly) > bound_deg) {
                                    use_interval_bound = true;
                                    break;
                                }
                            }
                        }
                    }
                }
            } else { // some roots are outside, thus we cannot use the interval bound
                use_interval_bound = false;
            }
        }
        if (!use_interval_bound) { // Connect ri_last with all roots above
            for (auto it = *ri_end; it != delin.roots().end(); it++) {
                for (const auto& t_root : it->second) {
                    if (*t_root.origin == poly) {
                        ordering.add_less(ri_last, t_root.root);
                    }
                }
            }
        } else { // Connect ri_first with interval.lower().value()
            if (std::prev(*ri_end)->first == proj.evaluate(ass, interval.upper().value()).first) {
                ordering.add_eq(ri_last, interval.lower().value());
                p_at_upper = true;
            } else {
                ordering.add_less(ri_last, interval.lower().value());
            }
        }
    }
    
    // Always-outside-roots: We make them non-optional, so they are considered in the further heuristic.
    for (auto it = delin.roots().begin(); it != delin.roots().end(); it++) {
        for (auto t_root : it->second) {
            if (t_root.origin && *t_root.origin == poly) {
                t_root.origin = std::nullopt;
                t_root.is_optional = false;
                t_root.is_inclusive = t_root.is_inclusive && ((!(it->first <= sample) || !p_at_lower) && (!(it->first >= sample) || !p_at_upper)); 
                delin.add_root(it->first, t_root);
            }
        }
        delin.remove_roots_with_origin(it->first, poly);
    }
}

inline void simplify(const datastructures::PolyRef poly, datastructures::Delineation& delin) {
    for (auto it = delin.roots().begin(); it != delin.roots().end(); it++) {
        for (auto t_root : it->second) {
            assert(t_root.origin || !t_root.is_optional);
            if (t_root.origin && *t_root.origin == poly) {
                t_root.origin = std::nullopt;
                t_root.is_optional = false;
                t_root.is_inclusive = false;
                delin.add_root(it->first, t_root);
            }
        }
        delin.remove_roots_with_origin(it->first, poly);
    }
}

}