#pragma once

#include "roots.h"
#include "derivation.h"

#include <boost/container/flat_set.hpp>

namespace smtrat::cadcells::datastructures {
    template<typename P>
    struct cell_representation {
        cell_description description;
        indexed_root_ordering ordering;
        boost::container::flat_set<poly_ref> equational;
        sampled_derivation<P>& derivation;

        cell_representation(sampled_derivation<P>& deriv) : derivation(deriv) {}
    };

    template<typename P>
    struct covering_representation {
        std::vector<cell_representation<P>> cells;
        covering_description get_covering() const {
            covering_description cov;
            for (const auto& cell : cells) {
                cov.add(cell.description);
            }
            return cov;
        }
        std::vector<std::reference_wrapper<sampled_derivation<P>>> sampled_derivations() {
            std::vector<std::reference_wrapper<sampled_derivation<P>>> cov;
            for (const auto& cell : cells) {
                cov.push_back(cell.derivation);
            }
            return cov;
        }
    };
}