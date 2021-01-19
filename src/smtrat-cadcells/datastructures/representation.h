#pragma once

#include "roots.h"
#include "derivation.h"

#include <boost/container/flat_set.hpp>

namespace smtrat::cadcells::datastructures {
    template<typename P>
    struct cell_representation {
        cell description;
        indexed_root_ordering ordering;
        boost::container::flat_set<poly_ref> equational;
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
        std::vector<derivation_ref<P>> sampled_derivations() {
            std::vector<derivation_ref<P>> cov;
            for (const auto& cell : cells) {
                cov.push_back(cell.derivation);
            }
            return cov;
        }
    };
}