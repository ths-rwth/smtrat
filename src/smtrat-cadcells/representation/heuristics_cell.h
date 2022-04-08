#include "../operators/properties.h"

namespace smtrat::cadcells::representation {

// TODO how to deal with trivial relations (indexed root expressions of the same polynomial?) and already ; part of heuristics? do not consider at all?

template<typename T>
inline void compute_section_all_equational(datastructures::SampledDerivationRef<T>& der, datastructures::CellRepresentation<T>& response) {
    for (const auto& poly : der->delin().nullified()) {
        response.equational.insert(poly);
    }
    for (const auto& poly : der->delin().nonzero()) {
        response.equational.insert(poly);
    }
    for (const auto& [ran,irexprs] : der->delin().roots()) {
        for (const auto& ir : irexprs) {
            if (/*ir.index == 1 &&*/ ir.poly != response.description.section_defining().poly) { // add poly only once
                response.equational.insert(ir.poly);
            }
        }
    }
}

template<typename T>
void maintain_connectedness(datastructures::SampledDerivationRef<T>& der, datastructures::CellRepresentation<T>& response) {
    if (der->contains(operators::properties::cell_connected{der->level()}) && response.description.is_sector() && response.description.lower() && response.description.upper()) {
        response.ordering.add_leq(*response.description.lower(), *response.description.upper());
    }
}

template <>
struct cell<CellHeuristic::BIGGEST_CELL> {
    template<typename T>
    static std::optional<datastructures::CellRepresentation<T>> compute(datastructures::SampledDerivationRef<T>& der) {
        datastructures::CellRepresentation<T> response(der);
        response.description = util::compute_simplest_cell(der->proj(), der->cell());

        if (der->cell().is_section()) {
            compute_section_all_equational(der, response);
        } else { // sector
            if (!der->delin().nullified().empty()) return std::nullopt;

            if (!der->cell().lower_unbounded()) {
                auto it = der->cell().lower();
                while(true) {
                    for (const auto& ir : it->second) {
                        if (ir != *response.description.lower()) {
                            response.ordering.add_leq(ir, *response.description.lower());
                        } 
                    }
                    if (it != der->delin().roots().begin()) it--;
                    else break;
                }
            }
            if (!der->cell().upper_unbounded()) {
                auto it = der->cell().upper();
                while(it != der->delin().roots().end()) {
                    for (const auto& ir : it->second) {
                        if (ir != *response.description.upper()) {
                            response.ordering.add_leq(*response.description.upper(), ir);
                        }
                    }
                    it++;
                }
            }
        }
        maintain_connectedness(der, response);
        return response;
    }
};

template <>
struct cell<CellHeuristic::CHAIN_EQ> {
    template<typename T>
    static std::optional<datastructures::CellRepresentation<T>> compute(datastructures::SampledDerivationRef<T>& der) {
        datastructures::CellRepresentation<T> response(der);
        response.description = util::compute_simplest_cell(der->proj(), der->cell());

        if (der->cell().is_section()) {
            compute_section_all_equational(der, response);
        } else { // sector
            if (!der->delin().nullified().empty()) return std::nullopt;

            if (!der->cell().lower_unbounded()) {
                boost::container::flat_set<datastructures::PolyRef> ignoring;
                auto it = der->cell().lower();
                auto barrier = *response.description.lower();
                while(true) {
                    auto simplest = util::simplest_bound(der->proj(), it->second, ignoring);
                    if (simplest) {
                        if (*simplest != *response.description.lower()) {
                            response.ordering.add_leq(*simplest, barrier);
                        }
                        for (const auto& ir : it->second) {
                            if (ignoring.contains(ir.poly)) continue;
                            if (ir != *simplest) {
                                response.ordering.add_leq(ir, *simplest);
                            } 
                            ignoring.insert(ir.poly);
                        }
                        barrier = *simplest;
                    }
                    if (it != der->delin().roots().begin()) it--;
                    else break;
                }
            }
            if (!der->cell().upper_unbounded()) {
                boost::container::flat_set<datastructures::PolyRef> ignoring;
                auto it = der->cell().upper();
                auto barrier = *response.description.upper();
                while(it != der->delin().roots().end()) {
                    auto simplest = util::simplest_bound(der->proj(), it->second, ignoring);
                    if (simplest) {
                        if (*simplest != *response.description.upper()) {
                            response.ordering.add_leq(barrier, *simplest);
                        }
                        for (const auto& ir : it->second) {
                            if (ignoring.contains(ir.poly)) continue;
                            if (ir != *simplest) {
                                response.ordering.add_leq(*simplest, ir);
                            } 
                            ignoring.insert(ir.poly);
                        }
                        barrier = *simplest;
                    }
                    it++;
                }
            }
        }
        maintain_connectedness(der, response);
        return response;
    }
};

template<typename T>
inline void compute_barriers(datastructures::SampledDerivationRef<T>& der, datastructures::CellRepresentation<T>& response, bool section) {
    while(section) {
        auto old_size = response.equational.size();

        auto it = der->cell().lower();
        while(true) {
            for (auto ir = it->second.begin(); ir != it->second.end(); ir++) {
                if (ir->poly == response.description.section_defining().poly) continue;
                if (response.equational.contains(ir->poly)) continue;
                if (!util::compare_simplest(der->proj(),ir->poly,response.description.section_defining().poly)) {
                    response.equational.insert(ir->poly);
                }
            }
            if (it != der->delin().roots().begin()) it--;
            else break;
        }

        it = der->cell().upper();
        while(it != der->delin().roots().end()) {
            for (auto ir = it->second.begin(); ir != it->second.end(); ir++) {
                if (ir->poly == response.description.section_defining().poly) continue;
                if (response.equational.contains(ir->poly)) continue;
                if (!util::compare_simplest(der->proj(),ir->poly,response.description.section_defining().poly)) {
                    response.equational.insert(ir->poly);
                }
            }
            it++;
        }

        if (old_size == response.equational.size()) {
            break;
        }
    }

    if (!der->cell().lower_unbounded())  {
        boost::container::flat_set<datastructures::PolyRef> ignoring;
        auto it = der->cell().lower();
        auto barrier = *response.description.lower_defining();
        while(true) {
            auto old_barrier = barrier;
            for (auto ir = it->second.begin(); ir != it->second.end(); ir++) {
                if (ignoring.contains(ir->poly)) continue;
                if (section && response.equational.contains(ir->poly)) continue;
                if (util::compare_simplest(der->proj(),ir->poly,barrier.poly)) {
                    barrier = *ir;
                }
            }
            assert(it != der->cell().lower() || barrier == *response.description.lower_defining());
            if (barrier != old_barrier) {
                response.ordering.add_leq(barrier, old_barrier);
            }
            for (const auto& ir : it->second) {
                if (ignoring.contains(ir.poly)) continue;
                if (section && response.equational.contains(ir.poly)) continue;
                if (ir != barrier) {
                    response.ordering.add_leq(ir, barrier);
                } 
                ignoring.insert(ir.poly);
            }
            if (it != der->delin().roots().begin()) it--;
            else break;
        }
    }
    if (!der->cell().upper_unbounded()) {
        boost::container::flat_set<datastructures::PolyRef> ignoring;
        auto it = der->cell().upper();
        auto barrier = *response.description.upper_defining();
        while(it != der->delin().roots().end()) {
            auto old_barrier = barrier;
            for (auto ir = it->second.begin(); ir != it->second.end(); ir++) {
                if (ignoring.contains(ir->poly)) continue;
                if (section && response.equational.contains(ir->poly)) continue;
                if (util::compare_simplest(der->proj(),ir->poly,barrier.poly)) {
                    barrier = *ir;
                }
            }
            assert(it != der->cell().upper() || barrier == *response.description.upper_defining());
            if (barrier != old_barrier) {
                response.ordering.add_leq(old_barrier, barrier);
            }
            for (const auto& ir : it->second) {
                if (ignoring.contains(ir.poly)) continue;
                if (section && response.equational.contains(ir.poly)) continue;
                if (ir != barrier) {
                    response.ordering.add_leq(barrier, ir);
                } 
                ignoring.insert(ir.poly);
            }
            it++;
        }
    }
}

template <>
struct cell<CellHeuristic::LOWEST_DEGREE_BARRIERS_EQ> {
    template<typename T>
    static std::optional<datastructures::CellRepresentation<T>> compute(datastructures::SampledDerivationRef<T>& der) {
        datastructures::CellRepresentation<T> response(der);
        response.description = util::compute_simplest_cell(der->proj(), der->cell());

        if (der->cell().is_section()) {
            compute_section_all_equational(der, response);
        } else { // sector
            if (!der->delin().nullified().empty()) return std::nullopt;
            compute_barriers(der, response, false);
        }
        maintain_connectedness(der, response);
        return response;
    }
};


template <>
struct cell<CellHeuristic::LOWEST_DEGREE_BARRIERS> {
    template<typename T>
    static std::optional<datastructures::CellRepresentation<T>> compute(datastructures::SampledDerivationRef<T>& der) {
        datastructures::CellRepresentation<T> response(der);
        response.description = util::compute_simplest_cell(der->proj(), der->cell());

        if (der->cell().is_section()) {
            for (const auto& poly : der->delin().nullified()) {
                response.equational.insert(poly);
            }
            for (const auto& poly : der->delin().nonzero()) {
                response.equational.insert(poly);
            }

            compute_barriers(der, response, true);
        } else { // sector
            if (!der->delin().nullified().empty()) return std::nullopt;
            compute_barriers(der, response, false);
        }
        maintain_connectedness(der, response);
        return response;
    }
};

}