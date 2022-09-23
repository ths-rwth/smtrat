#pragma once

#include "derivation.h"
#include "roots.h"

#include <boost/container/flat_set.hpp>

namespace smtrat::cadcells::datastructures {
/**
 * Represents a cell.
 */
template<typename P>
struct CellRepresentation {
    /// Description of a cell.
    SymbolicInterval description;
    /// An ordering on the roots that protects the cell.
    IndexedRootOrdering ordering;
    /// Polynomials that should be projected using the equational constraints projection.
    boost::container::flat_set<PolyRef> equational;
    /// Derivation
    SampledDerivationRef<P> derivation;

    CellRepresentation(SampledDerivationRef<P>& deriv)
        : derivation(deriv) {}
};
template<typename P>
inline std::ostream& operator<<(std::ostream& os, const CellRepresentation<P>& data) {
    os << "(cell: " << data.description << "; ordering: " << data.ordering << "; equational: " << data.equational << "; derivation: " << data.derivation << ")";
    return os;
}

/**
* Represents a covering over a cell.
* 
* The cells forming the covering are in increasing order (ordered by lower bound) and no cell is contained in another cell.
*/
template<typename P>
struct CoveringRepresentation {
    /// Cells of the covering in increasing order and no cell is contained in another cell.
    std::vector<CellRepresentation<P>> cells;
    /// An ordering on the roots for the cell boundaries mainting the covering.
    IndexedRootOrdering ordering;
    /// Returns a descriptions of the covering.
    CoveringDescription get_covering() const {
        assert(is_valid());
        CoveringDescription cov;
        for (const auto& cell : cells) {
            cov.add(cell.description);
        }
        return cov;
    }
    /// Returns the derivations.
    std::vector<SampledDerivationRef<P>> sampled_derivations() {
        std::vector<SampledDerivationRef<P>> cov;
        for (const auto& cell : cells) {
            cov.push_back(cell.derivation);
        }
        return cov;
    }

    /// Checks whether this represents a proper non-redundant covering.
    bool is_valid() const {
        auto cell = cells.begin();

        // covering
        if (!cell->derivation->cell().lower_unbounded()) return false;
        while (cell != std::prev(cells.end())) {
            cell++;
            if (std::prev(cell)->derivation->cell().upper_unbounded()) return false;
            if (cell->derivation->cell().lower_unbounded()) return false;
            if (upper_lt_lower(std::prev(cell)->derivation->cell(), cell->derivation->cell())) return false;
        }
        if (!cell->derivation->cell().upper_unbounded()) return false;

        // redundancy
        cell = cells.begin();
        while (cell != std::prev(cells.end())) {
            cell++;
            if (std::prev(cell)->derivation->cell().upper_unbounded()) return false;
            if (cell->derivation->cell().lower_unbounded()) return false;
            if (cell->derivation->cell().upper_unbounded()) continue;
            if (upper_lt_upper(cell->derivation->cell(), std::prev(cell)->derivation->cell()))  return false;
        }

        return true;
    }
};

template<typename P>
std::ostream& operator<<(std::ostream& os, const CoveringRepresentation<P>& data) {
    os << data.cells;
    return os;
}

} // namespace smtrat::cadcells::datastructures