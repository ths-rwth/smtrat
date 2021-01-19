#pragma once

#include "../datastructures/representation.h"

namespace smtrat::cadcells::representation {
    enum class cell_heuristic {
        DEFAULT
    };

    enum class covering_heuristic {
        DEFAULT
    };

    template<typename T, covering_heuristic H>
    std::optional<datastructures::covering_representation<T>> compute_covering_representation(const std::vector<datastructures::sampled_derivation_ref<T>>& ders);

    template<typename T, cell_heuristic H>
    std::optional<datastructures::cell_representation<T>> compute_cell_representation(datastructures::sampled_derivation_ref<T>& der);

    datastructures::indexed_root simplest_bound(const std::vector<datastructures::indexed_root>& bounds) { // TODO later: improve
        assert(!bound.empty());
        return *bounds.begin();
    }

    datastructures::cell compute_simplest_cell(const datastructures::delineation_cell& del) {
        if (del.is_section()) {
            return datastructures::cell(simplest_bound(del.lower()->second));
        } else if (del.lower_unbounded() && del.upper_unbounded()) {
            return datastructures::cell(datastructures::bound::infty, datastructures::bound::infty);
        } else if (del.lower_unbounded() ) {
            return datastructures::cell(datastructures::bound::infty, simplest_bound(del.upper()->second));
        } else if (del.upper_unbounded()) {
            return datastructures::cell(simplest_bound(del.lower()->second), datastructures::bound::infty);
        } else {
            return datastructures::cell(simplest_bound(del.lower()->second), simplest_bound(del.upper()->second));
        }
    }
    
    template<typename T>
    std::optional<datastructures::cell_representation<T>> compute_cell_representation<cell_heuristic::DEFAULT>(datastructures::sampled_derivation_ref<T>& der) {
        datastructures::cell_representation<T> response(der);
        response.description = compute_simplest_cell(der->cell());

        if (der->cell().is_section()) {
            for (const auto& poly : der->base()->delin().nullified()) {
                response.equational.insert(poly);
            }
            for (const auto& poly : der->base()->delin().nonzero()) {
                response.equational.insert(poly);
            }
            for (const auto& [ran,irexprs] : der->base()->delin().roots()) {
                for (const auto& ir : irexprs) {
                    if (ir.index == 1 && ir.poly != response.description.sector_defining().poly) { // add poly only once
                        response.equational.insert(ir.poly);
                    }
                }
            }
        } else { // sector
            if (!der->base()->delin().nullified().empty()) return std::nullopt;

            if (!der->cell().lower_unbounded()) {
                auto it = std::next(der->cell().lower());
                do {
                    it--;
                    for (const auto& ir : it->second) {
                        response.ordering.add_below(ir, *response.description.lower());
                    }
                } while(it != der->base()->delin().roots().begin());
            }
            if (!der->cell().upper_unbounded()) {
                auto it = der->cell().upper();
                do {
                    for (const auto& ir : it->second) {
                        response.ordering.add_above(*response.description.upper(), ir);
                    }
                    it++;
                } while(it != der->base()->delin().roots().end());
            }
        }
        return response;
    }

    template<typename T>
    std::optional<datastructures::covering_representation<T>> compute_covering_representation<covering_heuristic::DEFAULT>(const std::vector<datastructures::sampled_derivation_ref<T>>& ders) {
        datastructures::covering_representation<T> result;
        
        std::vector<datastructures::sampled_derivation_ref<T>> sorted_ders;
        for (auto& der : ders) sorted_ders.emplace_back(der);

        std::sort(sorted_ders.begin(), sorted_ders.end(), [](const datastructures::sampled_derivation_ref<T>& p_cell1, const datastructures::sampled_derivation_ref<T>& p_cell2) { // cell1 < cell2
            const auto& cell1 = p_cell1->cell();
            const auto& cell2 = p_cell1->cell();
            return lower_less(cell1, cell2) || (lower_equal(cell1, cell2) && upper_less(cell1, cell2));
        });

        auto iter = sorted_ders.begin();
        while (iter != sorted_ders.end()) {
            while (std::next(iter) != sorted_ders.end() && lower_equal((*iter)->cell(), (*std::next(iter))->cell()) && !upper_less((*std::next(iter))->cell(), (*iter)->cell())) iter++;
            auto cell_result = compute_cell_representation(*iter);
            if (!cell_result) return std::nullopt;
            result.cells.emplace_back(*cell_result);
            iter++;
        }

        return result;
    }


};