#pragma once

#include "roots.h"
#include "derivation.h"

namespace smtrat::cadcells::datastructures {
    template<typename Properties>
    struct cell_representation {
        cell description;
        indexed_root_ordering ordering;
        std::vector<poly_ref> equational;
        sampled_derivation_ref<Properties> derivation;
    };

    struct covering_representation {
        std::vector<cell_representation> cells;
        covering covering() {
            covering cov;
            for (const auto& cell : cell_representations) {
                cov.add(cell.description);
            }
            return cov;
        }
        std::vector<sampled_derivation_ref<Properties>> sampled_derivations() {
            std::vector<sampled_derivation_ref<Properties>> cov;
            for (const auto& cell : cell_representations) {
                cov.add(cell.base);
            }
            return cov;
        }
    };
}