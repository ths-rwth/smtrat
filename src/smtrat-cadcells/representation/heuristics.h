#pragma once

#include "../datastructures/representation.h"

namespace smtrat::cadcells::representation {
    enum cell_heuristic {
        default_cell
    };

    enum covering_heuristic {
        default_covering
    };

    template<cell_heuristic H>
    struct cell {
        template<typename T>
        static std::optional<datastructures::cell_representation<T>> compute(datastructures::sampled_derivation_ref<T>& der);
    };

    template<covering_heuristic H>
    struct covering {
        template<typename T>
        static std::optional<datastructures::covering_representation<T>> compute(const std::vector<datastructures::sampled_derivation_ref<T>>& ders);
    };

    template <>
    struct cell<cell_heuristic::default_cell> {
        static datastructures::indexed_root simplest_bound(const std::vector<datastructures::indexed_root>& bounds) { // TODO later: improve
            assert(!bounds.empty());
            return *bounds.begin();
        }

        static datastructures::cell_description compute_simplest_cell(const datastructures::delineation_cell& del) {
            if (del.is_section()) {
                return datastructures::cell_description(simplest_bound(del.lower()->second));
            } else if (del.lower_unbounded() && del.upper_unbounded()) {
                return datastructures::cell_description(datastructures::bound::infty, datastructures::bound::infty);
            } else if (del.lower_unbounded() ) {
                return datastructures::cell_description(datastructures::bound::infty, simplest_bound(del.upper()->second));
            } else if (del.upper_unbounded()) {
                return datastructures::cell_description(simplest_bound(del.lower()->second), datastructures::bound::infty);
            } else {
                return datastructures::cell_description(simplest_bound(del.lower()->second), simplest_bound(del.upper()->second));
            }
        }

        template<typename T>
        static std::optional<datastructures::cell_representation<T>> compute(datastructures::sampled_derivation_ref<T>& der) {
            datastructures::cell_representation<T> response(*der);
            response.description = compute_simplest_cell(der->cell());

            if (der->cell().is_section()) {
                for (const auto& poly : der->delin().nullified()) {
                    response.equational.insert(poly);
                }
                for (const auto& poly : der->delin().nonzero()) {
                    response.equational.insert(poly);
                }
                for (const auto& [ran,irexprs] : der->delin().roots()) {
                    for (const auto& ir : irexprs) {
                        if (ir.index == 1 && ir.poly != response.description.sector_defining().poly) { // add poly only once
                            response.equational.insert(ir.poly);
                        }
                    }
                }
            } else { // sector
                if (!der->delin().nullified().empty()) return std::nullopt;

                if (!der->cell().lower_unbounded()) {
                    auto it = std::next(der->cell().lower());
                    do {
                        it--;
                        for (const auto& ir : it->second) {
                            response.ordering.add_below(ir, *response.description.lower());
                        }
                    } while(it != der->delin().roots().begin());
                }
                if (!der->cell().upper_unbounded()) {
                    auto it = der->cell().upper();
                    do {
                        for (const auto& ir : it->second) {
                            response.ordering.add_above(*response.description.upper(), ir);
                        }
                        it++;
                    } while(it != der->delin().roots().end());
                }
            }
            return response;
        }
    };

    template <>
    struct covering<covering_heuristic::default_covering> {
        template<typename T>
        static std::optional<datastructures::covering_representation<T>> compute(const std::vector<datastructures::sampled_derivation_ref<T>>& ders) {
            datastructures::covering_representation<T> result;
            
            std::vector<datastructures::sampled_derivation_ref<T>> sorted_ders;
            for (auto& der : ders) sorted_ders.emplace_back(der);

            std::sort(sorted_ders.begin(), sorted_ders.end(), [](const datastructures::sampled_derivation_ref<T>& p_cell1, const datastructures::sampled_derivation_ref<T>& p_cell2) { // cell1 < cell2
                const auto& cell1 = p_cell1->cell();
                const auto& cell2 = p_cell2->cell();
                return lower_less(cell1, cell2) || (lower_equal(cell1, cell2) && upper_less(cell1, cell2));
            });

            auto iter = sorted_ders.begin();
            while (iter != sorted_ders.end()) {
                while (std::next(iter) != sorted_ders.end() && lower_equal((*iter)->cell(), (*std::next(iter))->cell()) && !upper_less((*std::next(iter))->cell(), (*iter)->cell())) iter++;
                std::optional<datastructures::cell_representation<T>> cell_result = cell<default_cell>::compute(*iter);
                if (!cell_result) return std::nullopt;
                result.cells.emplace_back(*cell_result);
                iter++;
            }

            return result;
        }
    };


};