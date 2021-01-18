#pragma once

#include "roots.h"
#include "derivation.h"

namespace smtrat::cadcells::datastructures {
    template<typename P>
    struct cell_representation {
        cell description;
        indexed_root_ordering ordering;
        std::vector<poly_ref> equational;
        sampled_derivation_ref<P> derivation;
    };

    template<typename P>
    struct covering_representation {
        std::vector<cell_representation<P>> cells;
        covering get_covering() const {
            covering cov;
            for (const auto& cell : cells) {
                cov.add(cell.description);
            }
            return cov;
        }
        std::vector<sampled_derivation_ref<P>> sampled_derivations() const {
            std::vector<sampled_derivation_ref<P>> cov;
            for (const auto& cell : cells) {
                cov.add(cell.base);
            }
            return cov;
        }
    };
}