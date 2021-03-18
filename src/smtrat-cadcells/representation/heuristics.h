#pragma once

#include "../datastructures/representation.h"

namespace smtrat::cadcells::representation {
    enum CellHeuristic {
        DEFAULT_CELL
    };

    enum CoveringHeuristic {
        DEFAULT_COVERING
    };

    template<CellHeuristic H>
    struct cell {
        template<typename T>
        static std::optional<datastructures::CellRepresentation<T>> compute(datastructures::SampledDerivationRef<T>& der);
    };

    template<CoveringHeuristic H>
    struct covering {
        template<typename T>
        static std::optional<datastructures::CoveringRepresentation<T>> compute(const std::vector<datastructures::SampledDerivationRef<T>>& ders);
    };

    template <>
    struct cell<CellHeuristic::DEFAULT_CELL> {
        static datastructures::IndexedRoot simplest_bound(const std::vector<datastructures::IndexedRoot>& bounds) { // TODO later: improve
            assert(!bounds.empty());
            return *bounds.begin();
        }

        static datastructures::CellDescription compute_simplest_cell(const datastructures::DelineationInterval& del) {
            if (del.is_section()) {
                return datastructures::CellDescription(simplest_bound(del.lower()->second));
            } else if (del.lower_unbounded() && del.upper_unbounded()) {
                return datastructures::CellDescription(datastructures::Bound::infty, datastructures::Bound::infty);
            } else if (del.lower_unbounded() ) {
                return datastructures::CellDescription(datastructures::Bound::infty, simplest_bound(del.upper()->second));
            } else if (del.upper_unbounded()) {
                return datastructures::CellDescription(simplest_bound(del.lower()->second), datastructures::Bound::infty);
            } else {
                return datastructures::CellDescription(simplest_bound(del.lower()->second), simplest_bound(del.upper()->second));
            }
        }

        template<typename T>
        static std::optional<datastructures::CellRepresentation<T>> compute(datastructures::SampledDerivationRef<T>& der) {
            datastructures::CellRepresentation<T> response(*der);
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
                        if (ir.index == 1 && ir.poly != response.description.section_defining().poly) { // add poly only once
                            response.equational.insert(ir.poly);
                        }
                    }
                }
            } else { // sector
                if (!der->delin().nullified().empty()) return std::nullopt;

                if (!der->cell().lower_unbounded()) {
                    auto it = der->cell().lower();
                    while(true) {
                        for (const auto& ir : it->second) {
                            if (ir != *response.description.lower()) {
                                response.ordering.add_below(ir, *response.description.lower());
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
                                response.ordering.add_above(*response.description.upper(), ir);
                            }
                        }
                        it++;
                    }
                }
            }
            return response;
        }
    };

    template <>
    struct covering<CoveringHeuristic::DEFAULT_COVERING> {
        template<typename T>
        static std::optional<datastructures::CoveringRepresentation<T>> compute(const std::vector<datastructures::SampledDerivationRef<T>>& ders) {
            datastructures::CoveringRepresentation<T> result;
            
            std::vector<datastructures::SampledDerivationRef<T>> sorted_ders;
            for (auto& der : ders) sorted_ders.emplace_back(der);

            std::sort(sorted_ders.begin(), sorted_ders.end(), [](const datastructures::SampledDerivationRef<T>& p_cell1, const datastructures::SampledDerivationRef<T>& p_cell2) { // cell1 < cell2
                const auto& cell1 = p_cell1->cell();
                const auto& cell2 = p_cell2->cell();
                return lower_less(cell1, cell2) || (lower_equal(cell1, cell2) && upper_less(cell2, cell1));
            });

            auto iter = sorted_ders.begin();
            while (iter != sorted_ders.end()) {
                std::optional<datastructures::CellRepresentation<T>> cell_result = cell<DEFAULT_CELL>::compute(*iter);
                if (!cell_result) return std::nullopt;
                result.cells.emplace_back(*cell_result);
                auto& last_cell = (*iter)->cell();
                iter++; 
                while (iter != sorted_ders.end() && !upper_less(last_cell, (*iter)->cell())) iter++;
            }

            return result;
        }
    };


};