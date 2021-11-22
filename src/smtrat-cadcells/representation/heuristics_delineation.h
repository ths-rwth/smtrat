namespace smtrat::cadcells::representation {

template <>
struct delineation<DelineationHeuristic::CHAIN> {
    template<typename T>
    static std::optional<datastructures::DelineationRepresentation<T>> compute(datastructures::DelineatedDerivationRef<T>& der) {
        datastructures::DelineationRepresentation<T> response(*der);

        if (!der->delin().nullified().empty()) return std::nullopt;

        if (der->delin().roots().empty()) return response;

        auto it = der->delin().roots().begin();
        auto barrier = util::simplest_bound(der->proj(), it->second);
        while(it != der->delin().roots().end()) {
            auto simplest = util::simplest_bound(der->proj(), it->second);
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