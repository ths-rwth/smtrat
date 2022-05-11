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

    inline std::string get_name(CellHeuristic heuristic){
        switch (heuristic) {
            case CellHeuristic::BIGGEST_CELL: return "BIGGEST_CELL";
            case CellHeuristic::CHAIN_EQ: return "CHAIN_EQ";
            case CellHeuristic::LOWEST_DEGREE_BARRIERS: return "LOWEST_DEGREE_BARRIERS";
            case CellHeuristic::LOWEST_DEGREE_BARRIERS_EQ: return "LOWEST_DEGREE_BARRIERS_EQ";
        }
    }

    inline std::string get_name(CoveringHeuristic heuristic){
        switch (heuristic) {
            case CoveringHeuristic::DEFAULT_COVERING: return "DEFAULT_COVERING";
            case CoveringHeuristic::CHAIN_COVERING: return "CHAIN_COVERING";
        }
    }

    inline std::string get_name(DelineationHeuristic heuristic){
        switch (heuristic) {
            case DelineationHeuristic::CHAIN: return "CHAIN";
        }
    }

    inline std::ostream& operator<<(std::ostream& os, CellHeuristic heuristic){
        return os << get_name(heuristic);
    }
    inline std::ostream& operator<<(std::ostream& os, CoveringHeuristic heuristic){
        return os << get_name(heuristic);
    }
    inline std::ostream& operator<<(std::ostream& os, DelineationHeuristic heuristic){
        return os << get_name(heuristic);
    }
}

#include "util.h"
#include "heuristics_cell.h"
#include "heuristics_covering.h"
#include "heuristics_delineation.h"

