namespace smtrat::cadcells::representation::util {

bool compare_simplest(datastructures::Projections& proj, datastructures::PolyRef p1, datastructures::PolyRef p2) {
    return proj.degree(p1) < proj.degree(p2);
    //return proj.max_degree(p1) < proj.max_degree(p2);
}
    
std::optional<datastructures::IndexedRoot> simplest_bound(datastructures::Projections& proj, const std::vector<datastructures::IndexedRoot>& bounds, const boost::container::flat_set<datastructures::PolyRef>& ignoring) {
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

datastructures::IndexedRoot simplest_bound(datastructures::Projections& proj, const std::vector<datastructures::IndexedRoot>& bounds) {
    boost::container::flat_set<datastructures::PolyRef> ignoring;
    return *simplest_bound(proj, bounds, ignoring);
}

datastructures::CellDescription compute_simplest_cell(datastructures::Projections& proj, const datastructures::DelineationInterval& del) {
    if (del.is_section()) {
        return datastructures::CellDescription(util::simplest_bound(proj, del.lower()->second));
    } else if (del.lower_unbounded() && del.upper_unbounded()) {
        return datastructures::CellDescription(datastructures::Bound::infty, datastructures::Bound::infty);
    } else if (del.lower_unbounded() ) {
        return datastructures::CellDescription(datastructures::Bound::infty, util::simplest_bound(proj, del.upper()->second));
    } else if (del.upper_unbounded()) {
        return datastructures::CellDescription(util::simplest_bound(proj, del.lower()->second), datastructures::Bound::infty);
    } else {
        return datastructures::CellDescription(util::simplest_bound(proj, del.lower()->second), util::simplest_bound(proj, del.upper()->second));
    }
}

std::optional<datastructures::GeneralIndexedRootOrdering> simplest_delineation_ordering(datastructures::Projections& proj, datastructures::Delineation& delin) {
    datastructures::GeneralIndexedRootOrdering ordering;

    if (!delin.nullified().empty()) return std::nullopt;
    if (delin.roots().empty()) return ordering;

    auto it = delin.roots().begin();
    auto barrier = simplest_bound(proj, it->second);
    while(it != delin.roots().end()) {
        auto simplest = simplest_bound(proj, it->second);
        if (barrier != simplest) {
            ordering.add(barrier, simplest);
        }
        for (const auto& ir : it->second) {
            if (ir != simplest) {
                ordering.add(simplest, ir);
            }
        }
        barrier = simplest;
        it++;
    }
    return ordering;
}

/// Assumes that the general ordering matches already the cell description. 
datastructures::IndexedRootOrdering cell_ordering_from_general(datastructures::GeneralIndexedRootOrdering& general, datastructures::CellDescription& cell) {
    datastructures::IndexedRootOrdering ordering;

    std::cout << general << std::endl; 

    // TODO we need reflixivity for general as well!

    if (cell.lower_defining()) {
        auto it = std::find_if(general.data().begin(), general.data().end(), [&cell](const auto& entry) {return entry.second == *cell.lower_defining(); } );
        if (it != general.data().end()) {
            assert(it+1 == general.data().end() || (it+1)->second != *cell.lower_defining()); // assumption for simpler implementation

            while(true) {
                ordering.add_below(it->second, it->first);
                if (it != general.data().begin()) it--;
                else break;
            }
        }
    }

    if (cell.upper_defining()) {
        auto it = std::find_if(general.data().begin(), general.data().end(), [&cell](const auto& entry) {return entry.first == *cell.upper_defining(); } );
        while(it != general.data().end()) {
            ordering.add_above(it->first, it->second);
            it++;
        }
    }

    if (cell.is_sector() && cell.lower_defining() && cell.upper_defining()) {
        // TODO this is messed up!
        auto it = std::find_if(general.data().begin(), general.data().end(), [&cell](const auto& entry) {return entry.second == *cell.lower_defining(); } );
        auto it_up = std::find_if(general.data().begin(), general.data().end(), [&cell](const auto& entry) {return entry.first == *cell.upper_defining(); } );
        it++;
        it_up--;


        while(true) {
            ordering.add_between(it->first, it->second);
            if (it == it_up) break;
            it++;
        }
    }

    return ordering;   

}

}