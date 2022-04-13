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

inline std::optional<datastructures::IndexedRootOrdering> simplest_delineation_ordering(datastructures::Projections& proj, datastructures::Delineation& delin) {
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

}