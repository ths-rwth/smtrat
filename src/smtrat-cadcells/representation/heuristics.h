#pragma once

#include "../datastructures/representation.h"

/**
 * @brief Heuristics for computing representations.
 * 
 */
namespace smtrat::cadcells::representation {
    enum CellHeuristic {
        BIGGEST_CELL, CHAIN_EQ, LOWEST_DEGREE_BARRIERS, LOWEST_DEGREE_BARRIERS_EQ, BIGGEST_CELL_EW
    };
    static const char * CellHeuristicStrings[] = { "BIGGEST_CELL", "CHAIN_EQ", "LOWEST_DEGREE_BARRIERS", "LOWEST_DEGREE_BARRIERS_EQ", "BIGGEST_CELL_EW" };

    enum CoveringHeuristic {
        DEFAULT_COVERING, CHAIN_COVERING, DEFAULT_COVERING_EW
    };
    static const char * CoveringHeuristicStrings[] = { "DEFAULT_COVERING", "CHAIN_COVERING", "DEFAULT_COVERING_EW" };

    enum DelineationHeuristic {
        CHAIN
    };
    static const char * DelineationHeuristicStrings[] = { "CHAIN" };

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

    inline std::ostream& operator<<(std::ostream& os, CellHeuristic heuristic){
        return os << CellHeuristicStrings[heuristic];
    }
    inline std::ostream& operator<<(std::ostream& os, CoveringHeuristic heuristic){
        return os << CoveringHeuristicStrings[heuristic];
    }
    inline std::ostream& operator<<(std::ostream& os, DelineationHeuristic heuristic){
        return os << DelineationHeuristicStrings[heuristic];
    }
}

#include "util.h"
#include "heuristics_cell.h"
#include "heuristics_covering.h"
#include "heuristics_delineation.h"

