namespace smtrat::cadcells::representation {

namespace util_del {
    std::optional<datastructures::IndexedRoot> simplest_bound(datastructures::Projections& proj, const std::vector<datastructures::IndexedRoot>& bounds, const boost::container::flat_set<datastructures::PolyRef>& ignoring) {
        assert(!bounds.empty());
        auto simplest = bounds.begin();
        for (auto iter = bounds.begin(); iter != bounds.end(); iter++) {
            if (ignoring.contains(iter->poly)) continue;
            if (proj.degree(iter->poly) < proj.degree(simplest->poly)) {
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

template <>
struct delineation<DelineationHeuristic::CHAIN> {
    template<typename T>
    static std::optional<datastructures::DelineationRepresentation<T>> compute(datastructures::DelineatedDerivationRef<T>& der) {
        datastructures::DelineationRepresentation<T> response(*der);

        if (!der->delin().nullified().empty()) return std::nullopt;

        auto it = der->delin().roots().begin();
        auto barrier = util_del::simplest_bound(der->proj(), it->second);
        while(it != der->delin().roots().end()) {
            auto simplest = util_del::simplest_bound(der->proj(), it->second);
            if (barrier != simplest) {
                response.ordering.add(barrier, simplest);
            }
            for (const auto& ir : it->second) {
                if (ir != simplest) {
                    response.ordering.add(simplest, ir);
                }
            }
            barrier = simplest;
            it++;
        }

        return response;
    }
};


}