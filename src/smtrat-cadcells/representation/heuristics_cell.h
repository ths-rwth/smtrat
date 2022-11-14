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
            if (/*ir.index == 1 &&*/ ir.root.poly != response.description.section_defining().poly) { // add poly only once
                response.equational.insert(ir.root.poly);
            }
        }
    }
}

template<typename T>
void maintain_connectedness(datastructures::SampledDerivationRef<T>& der, datastructures::CellRepresentation<T>& response, bool enable_weak = false) {
    if (der->contains(operators::properties::cell_connected{der->level()}) && !response.description.is_section() && !response.description.lower().is_infty() && !response.description.upper().is_infty()) {
        if (enable_weak) {
            response.ordering.add_leq(response.description.lower().value(), response.description.upper().value());
        } else {
            response.ordering.add_less(response.description.lower().value(), response.description.upper().value());
        }
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
struct cell<CellHeuristic::BIGGEST_CELL_EW> {
    template<typename T>
    static std::optional<datastructures::CellRepresentation<T>> compute(datastructures::SampledDerivationRef<T>& der) {
        datastructures::CellRepresentation<T> response(der);
        response.description = util::compute_simplest_cell(der->proj(), der->cell(), true);
        if (der->cell().is_section()) {
            compute_section_all_equational(der, response);
        } else { // sector
            datastructures::Delineation reduced_delineation;
            util::PolyDelineations poly_delins;
            util::decompose(der->delin(), der->cell(), reduced_delineation, poly_delins);
            auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
            auto res = util::simplest_biggest_cell_ordering(der->proj(), reduced_delineation, reduced_cell, response.description, true);
            if (!res) return std::nullopt;
            response.ordering = *res;
            for (const auto& poly_delin : poly_delins.data) {
                add_biggest_cell_ordering(response.ordering, poly_delin.first, poly_delin.second);
            }
            util::add_weird_ordering(response.ordering, der->delin(), der->cell(), response.description);
        }
        maintain_connectedness(der, response, true);
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
inline void compute_barriers(datastructures::SampledDerivationRef<T>& der, datastructures::CellRepresentation<T>& response, bool section, bool enable_weak = false) {
    // TODO refactor
    datastructures::Delineation reduced_delineation;
    util::PolyDelineations poly_delins;
    util::decompose(der->delin(), der->cell(), reduced_delineation, poly_delins);
    auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
    
    while(section) {
        auto old_size = response.equational.size();

        auto it = reduced_cell.lower();
        while(true) {
            for (auto ir = it->second.begin(); ir != it->second.end(); ir++) {
                if (ir->root.poly == response.description.section_defining().poly) continue;
                if (response.equational.contains(ir->root.poly)) continue;
                if (!util::compare_simplest(der->proj(),ir->root,response.description.section_defining())) {
                    response.equational.insert(ir->root.poly);
                }
            }
            if (it != reduced_delineation.roots().begin()) it--;
            else break;
        }

        it = reduced_cell.upper();
        while(it != reduced_delineation.roots().end()) {
            for (auto ir = it->second.begin(); ir != it->second.end(); ir++) {
                if (ir->root.poly == response.description.section_defining().poly) continue;
                if (response.equational.contains(ir->root.poly)) continue;
                if (!util::compare_simplest(der->proj(),ir->root,response.description.section_defining())) {
                    response.equational.insert(ir->root.poly);
                }
            }
            it++;
        }

        if (old_size == response.equational.size()) {
            break;
        }
    }

    boost::container::flat_map<datastructures::PolyRef, boost::container::flat_set<datastructures::PolyRef>> resultants;
    if (!reduced_cell.lower_unbounded()) {
        auto it = reduced_cell.lower();
        auto barrier = response.description.lower().value();
        bool barrier_incl = response.description.lower().is_weak();
        while(true) {
            auto old_barrier = barrier;
            bool old_barrier_incl = barrier_incl;
            for (auto ir = it->second.begin(); ir != it->second.end(); ir++) {
                if (section && response.equational.contains(ir->root.poly)) continue;
                if (util::compare_simplest(der->proj(),ir->root,barrier) || barrier == ir->root) {
                    if (barrier == ir->root) {
                        barrier_incl = ir->is_inclusive && barrier_incl;
                    }
                    barrier = ir->root;
                }
            }
            assert(it != reduced_cell.lower() || barrier == response.description.lower().value());
            if (barrier != old_barrier) {
                if (enable_weak && (response.description.lower().is_strict() || barrier_incl || !old_barrier_incl)) {
                    response.ordering.add_leq(barrier, old_barrier);
                } else {
                    response.ordering.add_less(barrier, old_barrier);
                }
                if (barrier.is_root() && old_barrier.is_root()) {
                    resultants.try_emplace(barrier.root().poly).first->second.insert(old_barrier.root().poly);
                    resultants.try_emplace(old_barrier.root().poly).first->second.insert(barrier.root().poly);
                }
            }
            for (const auto& ir : it->second) {
                if (section && response.equational.contains(ir.root.poly)) continue;
                if (ir.root != barrier) {
                    if (enable_weak && (response.description.lower().is_strict() || ir.is_inclusive || !barrier_incl)) {
                        response.ordering.add_leq(ir.root, barrier);
                    } else {
                        response.ordering.add_less(ir.root, barrier);
                    }
                    if (barrier.is_root()) {
                        resultants.try_emplace(ir.root.poly).first->second.insert(barrier.root().poly);
                        resultants.try_emplace(barrier.root().poly).first->second.insert(ir.root.poly);
                    }
                } 
            }
            if (it != reduced_delineation.roots().begin()) it--;
            else break;
        }
    }

    std::vector<datastructures::RootFunction> reached;
    if (!reduced_cell.upper_unbounded()) {
        auto it = reduced_cell.upper();
        auto barrier = response.description.upper().value();
        bool barrier_incl = response.description.upper().is_weak();
        reached.push_back(barrier);
        while(it != reduced_delineation.roots().end()) {
            auto old_barrier = barrier;
            bool old_barrier_incl = barrier_incl;
            for (auto ir = it->second.begin(); ir != it->second.end(); ir++) {
                if (section && response.equational.contains(ir->root.poly)) continue;
                if (util::compare_simplest(der->proj(),ir->root,barrier) || barrier == ir->root) {
                    if (barrier == ir->root) {
                        barrier_incl = ir->is_inclusive && barrier_incl;
                    }
                    barrier = ir->root;
                }
            }
            assert(it != reduced_cell.upper() || barrier == response.description.upper().value());
            if (barrier != old_barrier) {
                bool rchd = false;
                for (const auto& r : reached) {
                    if(barrier.is_root() && r.is_root() && resultants.try_emplace(barrier.root().poly).first->second.contains(r.root().poly)) {
                        if (enable_weak && response.description.upper().is_strict()) {
                            response.ordering.add_leq(r, barrier);
                        } else {
                            response.ordering.add_less(r, barrier);
                        }
                        rchd = true;
                    }
                }
                if (!rchd) {
                    if (enable_weak && (response.description.upper().is_strict() || barrier_incl || !old_barrier_incl)) {
                        response.ordering.add_leq(old_barrier, barrier);
                    } else {
                        response.ordering.add_less(old_barrier, barrier);
                    }
                }
                reached.push_back(barrier);
            }
            for (const auto& ir : it->second) {
                std::cout << ir << std::endl;
                if (section && response.equational.contains(ir.root.poly)) continue;
                if (ir.root != barrier) {
                    bool rchd = false;
                    for (const auto& r : reached) {
                        if(r.is_root() && resultants.try_emplace(ir.root.poly).first->second.contains(r.root().poly)) {
                            if (enable_weak && response.description.upper().is_strict()) {
                                response.ordering.add_leq(r, ir.root);
                            } else {
                                response.ordering.add_less(r, ir.root);
                            }
                            rchd = true;
                        }
                    }
                    if (!rchd) {
                        if (enable_weak && (response.description.upper().is_strict() || ir.is_inclusive || !barrier_incl)) {
                            response.ordering.add_leq(barrier, ir.root);
                        } else {
                            response.ordering.add_less(barrier, ir.root);
                        }
                    }
                    reached.push_back(ir.root);
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

template <>
struct cell<CellHeuristic::LOWEST_DEGREE_BARRIERS_EW> {
    template<typename T>
    static std::optional<datastructures::CellRepresentation<T>> compute(datastructures::SampledDerivationRef<T>& der) {
        datastructures::CellRepresentation<T> response(der);
        response.description = util::compute_simplest_cell(der->proj(), der->cell(), true);

        if (der->cell().is_section()) {
            for (const auto& poly : der->delin().nullified()) {
                response.equational.insert(poly);
            }
            for (const auto& poly : der->delin().nonzero()) {
                response.equational.insert(poly);
            }

            compute_barriers(der, response, true, true);
        } else { // sector
            if (!der->delin().nullified().empty()) return std::nullopt;
            compute_barriers(der, response, false, true);
            util::add_weird_ordering(response.ordering, der->delin(), der->cell(), response.description);
        }
        maintain_connectedness(der, response);
        return response;
    }
};

}