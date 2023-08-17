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

inline std::optional<datastructures::IndexedRoot> simplest_bound(datastructures::Projections& proj, const std::vector<datastructures::TaggedIndexedRoot>& bounds, const boost::container::flat_set<datastructures::PolyRef>& ignoring, bool enable_weak = false) {
    assert(!bounds.empty());
    auto simplest = bounds.begin();
    for (auto iter = bounds.begin(); iter != bounds.end(); iter++) {
        if (ignoring.contains(iter->root.poly)) continue;
        if (enable_weak && iter->is_inclusive != simplest->is_inclusive) {
            if (simplest->is_inclusive) {
                simplest = iter;
            }
        } else if (compare_simplest(proj,iter->root.poly,simplest->root.poly)) {
            simplest = iter;
        }
    }
    if (ignoring.contains(bounds.begin()->root.poly)) return std::nullopt;
    return simplest->root;
}

inline datastructures::IndexedRoot simplest_bound(datastructures::Projections& proj, const std::vector<datastructures::TaggedIndexedRoot>& bounds, bool enable_weak = false) {
    boost::container::flat_set<datastructures::PolyRef> ignoring;
    return *simplest_bound(proj, bounds, ignoring, enable_weak);
}

inline datastructures::SymbolicInterval compute_simplest_cell(datastructures::Projections& proj, const datastructures::DelineationInterval& del, bool enable_weak = false) {
    if (del.is_section()) {
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
        return datastructures::SymbolicInterval(lower, upper);
    }
}

inline std::optional<datastructures::IndexedRootOrdering> simplest_biggest_cell_ordering(datastructures::Projections& /*proj*/, datastructures::Delineation& delin, datastructures::DelineationInterval& delin_interval, const datastructures::SymbolicInterval& interval, bool enable_weak = false) {
    // assumes that interval is the simplest cell

    datastructures::IndexedRootOrdering ordering;

    if (!delin.nullified().empty()) return std::nullopt;
    if (delin.roots().empty()) return ordering;
    
    if (!delin_interval.lower_unbounded()) {
        auto it = delin_interval.lower();
        bool at_lower = true;
        while(true) {
            for (const auto& ir : it->second) {
                if (ir.root != interval.lower().value()) {
                    bool p_at_lower = std::find_if(delin_interval.lower()->second.begin(), delin_interval.lower()->second.end(), [&ir](const auto& tir) {
                        return tir.origin && *tir.origin == *ir.origin;
                    }) != delin_interval.lower()->second.end();
                    if (enable_weak && (interval.lower().is_strict() || (ir.is_inclusive && !p_at_lower))) {
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
                    bool p_at_upper = std::find_if(delin_interval.upper()->second.begin(), delin_interval.upper()->second.end(), [&ir](const auto& tir) {
                        return tir.origin && *tir.origin == *ir.origin;
                    }) != delin_interval.upper()->second.end();
                    if (enable_weak && (interval.upper().is_strict() || (ir.is_inclusive && !p_at_upper))) {
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
    return ordering;
}

inline std::optional<datastructures::IndexedRootOrdering> simplest_chain_ordering(datastructures::Projections& proj, datastructures::Delineation& delin, bool enable_weak = false) {
    assert(!enable_weak); // not supported

    datastructures::IndexedRootOrdering ordering;

    if (!delin.nullified().empty()) return std::nullopt;
    if (delin.roots().empty()) return ordering;

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
    return ordering;
}

struct PolyDelineation {
    boost::container::flat_set<std::size_t> delineated_roots;
    std::size_t critical_lower_root = 0;
    std::size_t critical_upper_root = 0;
};

struct PolyDelineations {
    boost::container::flat_map<datastructures::PolyRef,PolyDelineation> data;
    auto& get(const datastructures::PolyRef& poly) {
        if (data.find(poly) == data.end()) {
            data.emplace(poly, PolyDelineation());
        }
        return data[poly];
    }
};

inline void decompose(const datastructures::Delineation& delin, const datastructures::DelineationInterval& delin_interval, datastructures::Delineation& delin_out, PolyDelineations& poly_delin_out) {
    if (!delin_interval.lower_unbounded()) {
        // TODO can we leave out even more?
        boost::container::flat_set<std::pair<datastructures::PolyRef,std::optional<datastructures::PolyRef>>> seen;
        auto it = delin_interval.lower();
        while(true) {
            for (const auto& ir : it->second) {
                poly_delin_out.get(ir.root.poly).delineated_roots.insert(ir.root.index);
                if (seen.contains(std::make_pair(ir.root.poly,ir.origin))) continue;
                delin_out.add_root(it->first,ir);
                poly_delin_out.get(ir.root.poly).critical_lower_root = ir.root.index;
                seen.insert(std::make_pair(ir.root.poly,ir.origin));
            }
            if (it != delin.roots().begin()) it--;
            else break;
        }
    }
    if (!delin_interval.upper_unbounded()) {
        boost::container::flat_set<std::pair<datastructures::PolyRef,std::optional<datastructures::PolyRef>>> seen;
        auto it = delin_interval.upper();
        while(it != delin.roots().end()) {
            for (const auto& ir : it->second) {
                poly_delin_out.get(ir.root.poly).delineated_roots.insert(ir.root.index);
                if (seen.contains(std::make_pair(ir.root.poly,ir.origin))) continue;
                delin_out.add_root(it->first,ir);
                poly_delin_out.get(ir.root.poly).critical_upper_root = ir.root.index;
                seen.insert(std::make_pair(ir.root.poly,ir.origin));
            }
            it++;
        }
    }

    for (const auto& poly : delin.nullified()) {
        delin_out.add_poly_nullified(poly);
    }

    for (const auto& poly : delin.nonzero()) {
        delin_out.add_poly_nonzero(poly);
    }
}

inline void add_chain_ordering(datastructures::IndexedRootOrdering& out, const datastructures::PolyRef& poly, const PolyDelineation& poly_delin) {
    //assert(poly_delin.critical_lower_root == 0 && poly_delin.critical_upper_root == 0);
    for (auto it = poly_delin.delineated_roots.begin(); it != poly_delin.delineated_roots.end() && it != std::prev(poly_delin.delineated_roots.end()); it++) {
        out.add_less(datastructures::IndexedRoot(poly,*it),datastructures::IndexedRoot(poly,*(it+1)));
    }
}

inline void add_biggest_cell_ordering(datastructures::IndexedRootOrdering& out, const datastructures::PolyRef& poly, const PolyDelineation& poly_delin) {
    if (poly_delin.critical_lower_root != 0) {
            for (auto it = poly_delin.delineated_roots.begin(); *it != poly_delin.critical_lower_root; it++) {
            out.add_less(datastructures::IndexedRoot(poly,*it),datastructures::IndexedRoot(poly,poly_delin.critical_lower_root));
        }
    }
    if (poly_delin.critical_upper_root != 0) {
            for (auto it = poly_delin.delineated_roots.rbegin(); *it != poly_delin.critical_upper_root; it++) {
            out.add_less(datastructures::IndexedRoot(poly,poly_delin.critical_upper_root), datastructures::IndexedRoot(poly,*it));
        }
    }
}

inline void add_weird_ordering(datastructures::IndexedRootOrdering& out, const datastructures::Delineation& delin, const datastructures::DelineationInterval& delin_interval, const datastructures::SymbolicInterval& interval) {
    assert(!delin_interval.is_section());
    auto begin = delin_interval.lower_unbounded() ? delin.roots().begin() : std::next(delin_interval.lower());
    auto end = delin_interval.upper_unbounded() ? delin.roots().end() : delin_interval.upper();
    
    boost::container::flat_set<datastructures::PolyRef> polys;
    for (auto it = begin; it != end; it++) {
        for (const auto t_root : it->second) {
            polys.insert(*t_root.origin);
        }
    }

    for (const auto& p : polys) {
        bool p_at_lower = !delin_interval.lower_unbounded() && std::find_if(delin_interval.lower()->second.begin(), delin_interval.lower()->second.end(), [&p](const auto& tir) {
            return tir.origin && *tir.origin == p;
        }) != delin_interval.lower()->second.end();
        bool p_at_upper = !delin_interval.upper_unbounded() && std::find_if(delin_interval.upper()->second.begin(), delin_interval.upper()->second.end(), [&p](const auto& tir) {
            return tir.origin && *tir.origin == p;
        }) != delin_interval.upper()->second.end();

        datastructures::IndexedRoot prev;
        for (auto it = begin; it != end; it++) {
            for (const auto t_root : it->second) {
                bool same_value = false;
                if (*t_root.origin == p) {
                    if (prev == datastructures::IndexedRoot()) {
                        if (!interval.lower().is_infty() && interval.lower().value() != t_root.root) {
                            if (interval.lower().is_weak() && p_at_lower) {
                                out.add_eq(interval.lower().value(), t_root.root);
                            } else {
                                out.add_leq(interval.lower().value(), t_root.root);
                            }
                        }
                    } else {
                        if (same_value) out.add_eq(prev, t_root.root);
                        else out.add_less(prev, t_root.root);
                        same_value = true;
                    }
                    prev = t_root.root;
                }
            }
        }
        assert(prev != datastructures::IndexedRoot());
        if (!interval.upper().is_infty() && interval.upper().value() != prev) {
            if (interval.upper().is_weak() && p_at_upper) {
                out.add_eq(prev, interval.upper().value());
            } else {
                out.add_leq(prev, interval.upper().value());
            }
        }
    }
}

}