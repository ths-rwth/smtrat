#pragma once

#include "../datastructures/representation.h"

namespace smtrat::cadcells::representation {
    struct cell_heuristic {
        DEFAULT
    };

    struct covering_heuristic {
        DEFAULT
    };

    template<typename H, typename T>
    std::optional<datastructures::covering_representation<T>> compute_representation<H> (const std::vector<sampled_derivation_ref<T>>& ders);

    template<typename H, typename T>
    std::optional<datastructures::cell_representation<T>> compute_representation<H> (sampled_derivation_ref<T>& der);

    template<typename T>
    std::optional<datastructures::covering_representation<T>> compute_covering_representation<covering_heuristic::DEFAULT> (const std::vector<sampled_derivation_ref<T>>& ders) {
        datastructures::covering_representation<T> result;
        
        std::vector<sampled_derivation_ref<T>> sorted_ders;
        for (const auto& der : ders) sorted_ders.emplace_back(der);

        std::sort(sorted_ders.begin(), sorted_ders.end(), [](const sampled_derivation_ref<T> p_cell1, const sampled_derivation_ref<T> p_cell2) { // cell1 < cell2
            const auto& cell1 = p_cell1->cell_delin();
            const auto& cell2 = p_cell1->cell_delin();
            return lower_less(cell1, cell2) || (lower_equal(cell1, cell2) && upper_less(cell1, cell2));
        });

        auto iter = sorted_ders.begin();
        while (iter != sorted_cells.end()) {
            while (iter+1 != sorted_cells.end() && lower_equal(*iter, *(iter+1)) && !upper_less(cell2, cell1)) iter++;
            auto cell_result = compute_cell_representation(*iter);
            if (!cell_result) return std::nullopt;
            result.cells.emplace_back(*cell_result);
            iter++;
        }

        return result;
    }

    template<typename T>
    std::optional<datastructures::cell_representation<T>> compute_cell_representation<cell_heuristic::DEFAULT>(sampled_derivation_ref<T>& der) {
        cell_representation response;
        response.cell = compute_simplest_cell(der.delin());

        if (der.cell().is_section()) {
            for (const auto& poly : der.delin().nullified()) {
                response.equational.push_back(poly);
            }
            for (const auto& poly : der.delin().nonzero()) {
                response.equational.push_back(poly);
            }
            for (const auto& [ran,irexprs] : der.delin().roots()) {
                for (const auto& ir : irexprs) {
                    if (ir.idx == 1 && ir.poly != response.cell.sector_defining().poly) { // add poly only once
                        response.equational.push_back(ir.poly);
                    }
                }
            }
        } else { // sector
            if (!der.delin().nullified().empty()) return std::nullopt;

            if (!der.cell().lower_unbounded()) {
                auto it = der.cell().lower()+1;
                do {
                    it--;
                    for (const auto& ir : *it) {
                        response.ordering.add_below(std::make_pair(response.cell.lower(), ir));
                    }
                } while(it != der.delin().roots().begin())
            }
            if (!der.cell().upper_unbounded()) {
                auto it = der.cell().upper();
                do {
                    for (const auto& ir : *it) {
                        response.ordering.add_above(std::make_pair(response.cell.upper(), ir));
                    }
                    it++;
                } while(it != der.delin().roots().end())
            }
        }
        response.derivation = der;
        return response;
    }

    cell compute_simplest_cell(const delineation& del) {
        if (del.is_section()) {
            return cell(simplest_bound(*del.lower()));
        } else if (del.lower_unbounded() && del.upper_unbounded()) {
            return cell(INFTY, INFTY);
        } else if (del.lower_unbounded() ) {
            return cell(INFTY, simplest_bound(*del.upper()));
        } else if (del.upper_unbounded()) {
            return cell(simplest_bound(*del.lower()), INFTY);
        } else {
            return cell(simplest_bound(*del.lower()), simplest_bound(*del.upper()));
        }
    }

    indexed_root simplest_bound(const std::vector<indexed_root>& bounds) { // TODO later: improve
        assert(!bound.empty());
        return *bounds.begin();
    }


};