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
	CellDescription description;
	/// An ordering of the roots that protects the cell.
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
        std::vector<std::reference_wrapper<SampledDerivation<P>>> sampled_derivations() {
            std::vector<std::reference_wrapper<SampledDerivation<P>>> cov;
            for (const auto& cell : cells) {
                cov.push_back(cell.derivation);
            }
            return cov;
        }
        /// Checks whether this represents a proper non-redundant covering.
        bool is_valid() const {
            auto cell = cells.begin();

            // covering
            if (!cell->derivation.cell().lower_unbounded()) return false;
            while (cell != std::prev(cells.end())) {
                cell++;
                if (std::prev(cell)->derivation.cell().upper_unbounded()) return false;
                if (cell->derivation.cell().lower_unbounded()) return false;
                if (std::prev(cell)->derivation.cell().upper()->first < cell->derivation.cell().lower()->first) return false;
                if (std::prev(cell)->derivation.cell().upper()->first == cell->derivation.cell().lower()->first && std::prev(cell)->derivation.cell().is_sector() && cell->derivation.cell().is_sector()) return false;
            }
            if (!cell->derivation.cell().upper_unbounded()) return false;

            // redundancy
            cell = cells.begin();
            while (cell != std::prev(cells.end())) {
                cell++;
                if (std::prev(cell)->derivation.cell().upper_unbounded()) return false;
                if (cell->derivation.cell().upper_unbounded()) continue;
                if (std::prev(cell)->derivation.cell().upper()->first > cell->derivation.cell().upper()->first) return false;
                if (std::prev(cell)->derivation.cell().upper()->first == cell->derivation.cell().upper()->first && std::prev(cell)->derivation.cell().is_sector() && cell->derivation.cell().is_sector()) return false;
            }

            return true;
        }
    };
    template<typename P>
    std::ostream& operator<<(std::ostream& os, const CoveringRepresentation<P>& data) {
        os << data.cells;
        return os;
    }

    /**
     * Represents a delineation.
     */
    template<typename P>
    struct DelineationRepresentation {
        /// An ordering of the roots that represents the delineation.
        GeneralIndexedRootOrdering ordering;
        /// Derivation.
        DelineatedDerivation<P>& derivation;

        DelineationRepresentation(DelineatedDerivation<P>& deriv) : derivation(deriv) {}
    };
    template<typename P>
    std::ostream& operator<<(std::ostream& os, const DelineationRepresentation<P>& data) {
        os << "(ordering: " << data.ordering << "; derivation: " << &data.derivation << ")";
        return os;
    }
}