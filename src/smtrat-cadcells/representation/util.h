namespace smtrat::cadcells::representation::util {

inline bool compare_simplest(datastructures::Projections& proj, datastructures::PolyRef p1, datastructures::PolyRef p2) {
    return proj.degree(p1) < proj.degree(p2);
    //return proj.max_degree(p1) < proj.max_degree(p2);
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
        while(true) {
            for (const auto& ir : it->second) {
                if (ir.root != interval.lower().value()) {
                    if (enable_weak && (interval.lower().is_strict() || ir.is_inclusive)) {
                        ordering.add_leq(ir.root, interval.lower().value());
                    } else {
                        ordering.add_less(ir.root, interval.lower().value());
                    }
                    
                } 
            }
            if (it != delin.roots().begin()) it--;
            else break;
        }
    }
    if (!delin_interval.upper_unbounded()) {
        auto it = delin_interval.upper();
        while(it != delin.roots().end()) {
            for (const auto& ir : it->second) {
                if (ir.root != interval.upper().value()) {
                    if (enable_weak && (interval.upper().is_strict() || ir.is_inclusive)) {
                        ordering.add_leq(interval.upper().value(), ir.root);
                    } else {
                        ordering.add_less(interval.upper().value(), ir.root);
                    }
                }
            }
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
        boost::container::flat_set<datastructures::PolyRef> seen;
        auto it = delin_interval.lower();
        while(true) {
            for (const auto& ir : it->second) {
                poly_delin_out.get(ir.root.poly).delineated_roots.insert(ir.root.index);
                if (seen.contains(ir.root.poly)) continue;
                delin_out.add_root(it->first,ir.root,ir.is_inclusive);
                poly_delin_out.get(ir.root.poly).critical_lower_root = ir.root.index;
                seen.insert(ir.root.poly);
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
                poly_delin_out.get(ir.root.poly).delineated_roots.insert(ir.root.index);
                if (seen.contains(ir.root.poly)) continue;
                delin_out.add_root(it->first,ir.root,ir.is_inclusive);
                poly_delin_out.get(ir.root.poly).critical_upper_root = ir.root.index;
                seen.insert(ir.root.poly);
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
    assert(poly_delin.critical_lower_root == 0 && poly_delin.critical_lower_root == 0);
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

}