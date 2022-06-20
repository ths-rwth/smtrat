namespace smtrat::cadcells::representation::util {

inline bool compare_simplest(datastructures::Projections& proj, datastructures::PolyRef p1, datastructures::PolyRef p2) {
    return proj.degree(p1) < proj.degree(p2);
    //return proj.max_degree(p1) < proj.max_degree(p2);
}
    
inline std::optional<datastructures::IndexedRoot> simplest_bound(datastructures::Projections& proj, const std::vector<datastructures::IndexedRoot>& bounds, const boost::container::flat_set<datastructures::PolyRef>& ignoring) {
    assert(!bounds.empty());
    auto simplest = bounds.begin();
    for (auto iter = bounds.begin(); iter != bounds.end(); iter++) {
        if (ignoring.contains(iter->poly)) continue;
        if (compare_simplest(proj,iter->poly,simplest->poly)) {
            simplest = iter;
        }
    }
    if (ignoring.contains(bounds.begin()->poly)) return std::nullopt;
    return *simplest;
}

inline datastructures::IndexedRoot simplest_bound(datastructures::Projections& proj, const std::vector<datastructures::IndexedRoot>& bounds) {
    boost::container::flat_set<datastructures::PolyRef> ignoring;
    return *simplest_bound(proj, bounds, ignoring);
}

inline datastructures::SymbolicInterval compute_simplest_cell(datastructures::Projections& proj, const datastructures::DelineationInterval& del) {
    if (del.is_section()) {
        return datastructures::SymbolicInterval(util::simplest_bound(proj, del.lower()->second));
    } else if (del.lower_unbounded() && del.upper_unbounded()) {
        return datastructures::SymbolicInterval(datastructures::Bound::infty(), datastructures::Bound::infty());
    } else if (del.lower_unbounded()) {
        return datastructures::SymbolicInterval(datastructures::Bound::infty(), datastructures::Bound::strict(util::simplest_bound(proj, del.upper()->second)));
    } else if (del.upper_unbounded()) {
        return datastructures::SymbolicInterval(datastructures::Bound::strict(util::simplest_bound(proj, del.lower()->second)), datastructures::Bound::infty());
    } else {
        return datastructures::SymbolicInterval(datastructures::Bound::strict(util::simplest_bound(proj, del.lower()->second)), datastructures::Bound::strict(util::simplest_bound(proj, del.upper()->second)));
    }
}

inline std::optional<datastructures::IndexedRootOrdering> simplest_biggest_cell_ordering(datastructures::Projections& /*proj*/, datastructures::Delineation& delin, datastructures::DelineationInterval& delin_interval, const datastructures::SymbolicInterval& interval) {
    // assumes that interval is the simplest cell

    datastructures::IndexedRootOrdering ordering;

    if (!delin.nullified().empty()) return std::nullopt;
    if (delin.roots().empty()) return ordering;
    
    if (!delin_interval.lower_unbounded()) {
        auto it = delin_interval.lower();
        while(true) {
            for (const auto& ir : it->second) {
                if (ir != interval.lower().value()) {
                    ordering.add_leq(ir, interval.lower().value());
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
                if (ir != interval.upper().value()) {
                    ordering.add_leq(interval.upper().value(), ir);
                }
            }
            it++;
        }
    }
    return ordering;
}

inline std::optional<datastructures::IndexedRootOrdering> simplest_chain_ordering(datastructures::Projections& proj, datastructures::Delineation& delin) {
    datastructures::IndexedRootOrdering ordering;

    if (!delin.nullified().empty()) return std::nullopt;
    if (delin.roots().empty()) return ordering;

    auto it = delin.roots().begin();
    auto barrier = simplest_bound(proj, it->second);
    while(it != delin.roots().end()) {
        auto simplest = simplest_bound(proj, it->second);
        if (barrier != simplest) {
            ordering.add_leq(barrier, simplest);
        }
        for (const auto& ir : it->second) {
            if (ir != simplest) {
                ordering.add_eq(simplest, ir);
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
                poly_delin_out.get(ir.poly).delineated_roots.insert(ir.index);
                if (seen.contains(ir.poly)) continue;
                delin_out.add_root(it->first,ir);
                poly_delin_out.get(ir.poly).critical_lower_root = ir.index;
                seen.insert(ir.poly);
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
                poly_delin_out.get(ir.poly).delineated_roots.insert(ir.index);
                if (seen.contains(ir.poly)) continue;
                delin_out.add_root(it->first,ir);
                poly_delin_out.get(ir.poly).critical_upper_root = ir.index;
                seen.insert(ir.poly);
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
        out.add_leq(datastructures::IndexedRoot(poly,*it),datastructures::IndexedRoot(poly,*(it+1)));
    }
}

inline void add_biggest_cell_ordering(datastructures::IndexedRootOrdering& out, const datastructures::PolyRef& poly, const PolyDelineation& poly_delin) {
    if (poly_delin.critical_lower_root != 0) {
            for (auto it = poly_delin.delineated_roots.begin(); *it != poly_delin.critical_lower_root; it++) {
            out.add_leq(datastructures::IndexedRoot(poly,*it),datastructures::IndexedRoot(poly,poly_delin.critical_lower_root));
        }
    }
    if (poly_delin.critical_upper_root != 0) {
            for (auto it = poly_delin.delineated_roots.rbegin(); *it != poly_delin.critical_upper_root; it++) {
            out.add_leq(datastructures::IndexedRoot(poly,poly_delin.critical_upper_root), datastructures::IndexedRoot(poly,*it));
        }
    }
}

}