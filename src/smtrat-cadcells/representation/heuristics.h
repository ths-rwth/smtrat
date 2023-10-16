#pragma once

#include "../datastructures/representation.h"

/**
 * @brief Heuristics for computing representations.
 * 
 */
namespace smtrat::cadcells::representation {
    enum CellHeuristic {
        BIGGEST_CELL, CHAIN_EQ, LOWEST_DEGREE_BARRIERS, LOWEST_DEGREE_BARRIERS_EQ, BIGGEST_CELL_FILTER, BIGGEST_CELL_FILTER_ONLY_INDEPENDENT, LOWEST_DEGREE_BARRIERS_FILTER, LOWEST_DEGREE_BARRIERS_FILTER_ONLY_INDEPENDENT, BIGGEST_CELL_APPROXIMATION, BIGGEST_CELL_PDEL, LOWEST_DEGREE_BARRIERS_PDEL, LOWEST_DEGREE_BARRIERS_CACHE_GLOBAL
    };
    static const char * CellHeuristicStrings[] = { "BIGGEST_CELL", "CHAIN_EQ", "LOWEST_DEGREE_BARRIERS", "LOWEST_DEGREE_BARRIERS_EQ", "BIGGEST_CELL_FILTER", "BIGGEST_CELL_FILTER_ONLY_INDEPENDENT", "LOWEST_DEGREE_BARRIERS_FILTER", "LOWEST_DEGREE_BARRIERS_FILTER_ONLY_INDEPENDENT", "BIGGEST_CELL_PDEL", "LOWEST_DEGREE_BARRIERS_PDEL", "LOWEST_DEGREE_BARRIERS_CACHE_GLOBAL" };

    enum CoveringHeuristic {
        BIGGEST_CELL_COVERING, CHAIN_COVERING, BIGGEST_CELL_COVERING_FILTER, BIGGEST_CELL_COVERING_FILTER_ONLY_INDEPENDENT, BIGGEST_CELL_COVERING_MIN_TDEG, BIGGEST_CELL_COVERING_PDEL, LDB_COVERING, LDB_COVERING_CACHE, LDB_COVERING_CACHE_GLOBAL
    };
    static const char * CoveringHeuristicStrings[] = { "BIGGEST_CELL_COVERING", "CHAIN_COVERING", "BIGGEST_CELL_COVERING_FILTER", "BIGGEST_CELL_COVERING_FILTER_ONLY_INDEPENDENT", "BIGGEST_CELL_COVERING_MIN_TDEG", "BIGGEST_CELL_COVERING_PDEL", "LDB_COVERING", "LDB_COVERING_CACHE", "LDB_COVERING_CACHE_GLOBAL" };

    /**
     * Note: If connected(i) holds, then the indexed root ordering must contain an ordering between the interval bounds. 
     */
    template<CellHeuristic H>
    struct cell {
        template<typename T>
        static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der);
    };

    template<CoveringHeuristic H>
    struct covering {
        template<typename T>
        static datastructures::CoveringRepresentation<T> compute(const std::vector<datastructures::SampledDerivationRef<T>>& ders);
    };

    inline std::ostream& operator<<(std::ostream& os, CellHeuristic heuristic){
        return os << CellHeuristicStrings[heuristic];
    }
    inline std::ostream& operator<<(std::ostream& os, CoveringHeuristic heuristic){
        return os << CoveringHeuristicStrings[heuristic];
    }
}

#include "util.h"
#include "heuristics_cell.h"
#include "heuristics_covering.h"
#include "heuristics_approximation.h"
