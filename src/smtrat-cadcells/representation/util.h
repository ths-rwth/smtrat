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

}