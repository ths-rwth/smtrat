#pragma once

#include "roots.h"
#include "derivation.h"

namespace smtrat::cadcells::datastructures {
    struct cell_representation {
        cell interval;
        indexed_root_ordering ordering;
        std::vector<poly_ref> equational;
        const cell_derivation& base; // TODO better solution?
    };

    struct covering_representation {
        std::vector<cell_representation> cells;
        covering covering() {
            covering cov;
            for (const auto& cell_repr : cell_representations) {
                cov.push_back(cell_repr.cell);
            }
            return cov;
        }
    };
}