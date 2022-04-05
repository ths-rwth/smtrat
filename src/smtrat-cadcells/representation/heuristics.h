#pragma once

#include "../datastructures/representation.h"

/**
 * @brief Heuristics for computing representations.
 * 
 */
namespace smtrat::cadcells::representation {
    enum CellHeuristic {
        BIGGEST_CELL, CHAIN_EQ, LOWEST_DEGREE_BARRIERS, LOWEST_DEGREE_BARRIERS_EQ
    };

    enum CoveringHeuristic {
        DEFAULT_COVERING, CHAIN_COVERING
    };

    enum DelineationHeuristic {
        CHAIN
    };

    /**
     * Note: If connected(i) holds, then the indexed root ordering must contain an ordering between the interval bounds. 
     */
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

    template<DelineationHeuristic H>
    struct delineation {
        template<typename T>
        static std::optional<datastructures::DelineationRepresentation<T>> compute(datastructures::DelineatedDerivationRef<T>& der);
    };
}

#include "util.h"
#include "heuristics_cell.h"
#include "heuristics_covering.h"
#include "heuristics_delineation.h"

