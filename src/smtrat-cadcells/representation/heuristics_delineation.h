namespace smtrat::cadcells::representation {

template <>
struct delineation<DelineationHeuristic::CHAIN> {
    template<typename T>
    static std::optional<datastructures::DelineationRepresentation<T>> compute(datastructures::DelineatedDerivationRef<T>& der) {
        datastructures::DelineationRepresentation<T> response(der);
        if (!der->delin().nullified().empty()) return std::nullopt;
        response.ordering = *util::simplest_delineation_ordering(der->proj(), der->delin());
        return response;
    }
};


}