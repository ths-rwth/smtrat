#pragma once

#include "roots.h"
#include "derivation.h"

#include <boost/container/flat_set.hpp>

namespace smtrat::cadcells::datastructures {
    /**
     * Represents a cell.
     */
    template<typename P>
    struct cell_representation {
        /// Description of a cell.
        cell_description description;
        /// An ordering of the roots that protects the cell.
        indexed_root_ordering ordering;
        /// Polynomials that should be projected using the equational constraints projection.
        boost::container::flat_set<poly_ref> equational;
        /// Derivation.
        sampled_derivation<P>& derivation;

        cell_representation(sampled_derivation<P>& deriv) : derivation(deriv) {}
    };
    template<typename P>
    std::ostream& operator<<(std::ostream& os, const cell_representation<P>& data) {
        os << "(cell: " << data.description << "; ordering: " << data.ordering << "; equational: " << data.equational << "; derivation: " << &data.derivation << ")";
        return os;
    }

    /**
     * Represents a covering over a cell.
     * 
     * The cells forming the covering are in increasing order and no cell is contained in another cell.
     */
    template<typename P>
    struct covering_representation {
        /// Cells of the covering in increasing order and no cell is contained in another cell.
        std::vector<cell_representation<P>> cells;
        /// Returns a descriptions of the covering.
        covering_description get_covering() const {
            assert(is_valid());
            covering_description cov;
            for (const auto& cell : cells) {
                cov.add(cell.description);
            }
            return cov;
        }
        /// Returns the derivations.
        std::vector<std::reference_wrapper<sampled_derivation<P>>> sampled_derivations() {
            std::vector<std::reference_wrapper<sampled_derivation<P>>> cov;
            for (const auto& cell : cells) {
                cov.push_back(cell.derivation);
            }
            return cov;
        }
        bool is_valid() const { // TODO extend for redundancy checks
            auto cell = cells.begin();

            if (!cell->derivation.cell().lower_unbounded()) return false;
            while (cell != std::prev(cells.end())) {
                cell++;
                if (std::prev(cell)->derivation.cell().upper_unbounded()) return false;
                if (cell->derivation.cell().lower_unbounded()) return false;
                if (std::prev(cell)->derivation.cell().upper()->first <= cell->derivation.cell().lower()->first) return false;
            }
            if (!cell->derivation.cell().upper_unbounded()) return false;
            return true;
        }
    };
    template<typename P>
    std::ostream& operator<<(std::ostream& os, const covering_representation<P>& data) {
        os << data.cells;
        return os;
    }
}