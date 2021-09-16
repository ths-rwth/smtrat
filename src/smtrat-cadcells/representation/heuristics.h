#pragma once

#include "../datastructures/representation.h"

namespace smtrat::cadcells::representation {
    enum CellHeuristic {
        BIGGEST_CELL, CHAIN_EQ, LOWEST_DEGREE_BARRIERS, LOWEST_DEGREE_BARRIERS_EQ
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
}

#include "heuristics_cell.h"
    
namespace smtrat::cadcells::representation {
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
                std::optional<datastructures::CellRepresentation<T>> cell_result = cell<BIGGEST_CELL>::compute(*iter);
                if (!cell_result) return std::nullopt;
                result.cells.emplace_back(*cell_result);
                auto& last_cell = (*iter)->cell();
                iter++; 
                while (iter != sorted_ders.end() && !upper_less(last_cell, (*iter)->cell())) iter++;
            }

            return result;
        }
    };
}