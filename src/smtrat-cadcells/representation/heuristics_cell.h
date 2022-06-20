#include "../operators/properties.h"

namespace smtrat::cadcells::representation {

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
    if (der->contains(operators::properties::cell_connected{der->level()}) && !response.description.is_section() && !response.description.lower().is_infty() && !response.description.upper().is_infty()) {
        response.ordering.add_leq(response.description.lower().value(), response.description.upper().value());
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
            // auto res = simplest_biggest_cell_ordering(der->proj(), der->delin(), der->cell(), response.description);
            // if (!res) return std::nullopt;
            // response.ordering = *res;
            datastructures::Delineation reduced_delineation;
            util::PolyDelineations poly_delins;
            util::decompose(der->delin(), der->cell(), reduced_delineation, poly_delins);
            auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
            auto res = util::simplest_biggest_cell_ordering(der->proj(), reduced_delineation, reduced_cell, response.description);
            if (!res) return std::nullopt;
            response.ordering = *res;
            for (const auto& poly_delin : poly_delins.data) {
                add_biggest_cell_ordering(response.ordering, poly_delin.first, poly_delin.second);
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

            datastructures::Delineation reduced_delineation;
            util::PolyDelineations poly_delins;
            util::decompose(der->delin(), der->cell(), reduced_delineation, poly_delins);
            auto res = util::simplest_chain_ordering(der->proj(), reduced_delineation);
            if (!res) return std::nullopt;
            response.ordering = *res;
            for (const auto& poly_delin : poly_delins.data) {
                add_biggest_cell_ordering(response.ordering, poly_delin.first, poly_delin.second);
            }
        }
        maintain_connectedness(der, response);
        return response;
    }
};

template<typename T>
inline void compute_barriers(datastructures::SampledDerivationRef<T>& der, datastructures::CellRepresentation<T>& response, bool section) {
    datastructures::Delineation reduced_delineation;
    util::PolyDelineations poly_delins;
    util::decompose(der->delin(), der->cell(), reduced_delineation, poly_delins);
    auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
    
    while(section) {
        auto old_size = response.equational.size();

        auto it = reduced_cell.lower();
        while(true) {
            for (auto ir = it->second.begin(); ir != it->second.end(); ir++) {
                if (ir->poly == response.description.section_defining().poly) continue;
                if (response.equational.contains(ir->poly)) continue;
                if (!util::compare_simplest(der->proj(),ir->poly,response.description.section_defining().poly)) {
                    response.equational.insert(ir->poly);
                }
            }
            if (it != reduced_delineation.roots().begin()) it--;
            else break;
        }

        it = reduced_cell.upper();
        while(it != reduced_delineation.roots().end()) {
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

    boost::container::flat_map<datastructures::PolyRef, boost::container::flat_set<datastructures::PolyRef>> resultants;
    if (!reduced_cell.lower_unbounded())  {
        auto it = reduced_cell.lower();
        auto barrier = response.description.lower().value();
        while(true) {
            auto old_barrier = barrier;
            for (auto ir = it->second.begin(); ir != it->second.end(); ir++) {
                if (section && response.equational.contains(ir->poly)) continue;
                if (util::compare_simplest(der->proj(),ir->poly,barrier.poly)) {
                    barrier = *ir;
                }
            }
            assert(it != reduced_cell.lower() || barrier == response.description.lower().value());
            if (barrier != old_barrier) {
                response.ordering.add_leq(barrier, old_barrier);
                resultants.try_emplace(barrier.poly).first->second.insert(old_barrier.poly);
                resultants.try_emplace(old_barrier.poly).first->second.insert(barrier.poly);
            }
            for (const auto& ir : it->second) {
                if (section && response.equational.contains(ir.poly)) continue;
                if (ir != barrier) {
                    response.ordering.add_leq(ir, barrier);
                    resultants.try_emplace(ir.poly).first->second.insert(barrier.poly);
                    resultants.try_emplace(barrier.poly).first->second.insert(ir.poly);
                } 
            }
            if (it != reduced_delineation.roots().begin()) it--;
            else break;
        }
    }

    std::vector<datastructures::IndexedRoot> reached;
    if (!reduced_cell.upper_unbounded()) {
        auto it = reduced_cell.upper();
        auto barrier = response.description.upper().value();
        reached.push_back(barrier);
        while(it != reduced_delineation.roots().end()) {
            auto old_barrier = barrier;
            for (auto ir = it->second.begin(); ir != it->second.end(); ir++) {
                if (section && response.equational.contains(ir->poly)) continue;
                if (util::compare_simplest(der->proj(),ir->poly,barrier.poly)) {
                    barrier = *ir;
                }
            }
            assert(it != reduced_cell.upper() || barrier == response.description.upper().value());
            if (barrier != old_barrier) {
                bool rchd = false;
                for (const auto r : reached) {
                    if(resultants.try_emplace(barrier.poly).first->second.contains(r.poly)) {
                        response.ordering.add_leq(r, barrier);
                        rchd = true;
                    }
                }
                if (!rchd) {
                    response.ordering.add_leq(old_barrier, barrier);
                }
                reached.push_back(barrier);
            }
            for (const auto& ir : it->second) {
                if (section && response.equational.contains(ir.poly)) continue;
                if (ir != barrier) {
                    bool rchd = false;
                    for (const auto r : reached) {
                        if(resultants.try_emplace(ir.poly).first->second.contains(r.poly)) {
                            response.ordering.add_leq(r, ir);
                            rchd = true;
                        }
                    }
                    if (!rchd) {
                        response.ordering.add_leq(barrier, ir);
                    }
                    reached.push_back(ir);
                } 
            }
            it++;
        }
    }

    for (const auto& poly_delin : poly_delins.data) {
        if (section && response.equational.contains(poly_delin.first)) continue;
        add_biggest_cell_ordering(response.ordering, poly_delin.first, poly_delin.second);
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