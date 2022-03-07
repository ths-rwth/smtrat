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
			cov.push_back(*cell.derivation);
		}
		return cov;
	}

	std::vector<SampledDerivationRef<P>> sampled_derivation_refs() {
		std::vector<SampledDerivationRef<P>> cov;
		for (const auto& cell : cells) {
			cov.push_back(cell.derivation);
		}
		return cov;
	}

	/**
	 * @brief Search of a sample point outside of the cells of the covering. 
	 * 
	 * @param reference to a RAN, in which the sample point is written, if one can be found
	 * @return size_t indicating whether a sample point has been found: 0 iff sample point has been found, 1 otherwise.
	 */
	size_t sample_outside(RAN& sample) const {

		SMTRAT_LOG_DEBUG("smtrat.covering", "Sampling Outside of: " << *this)


		if (cells.empty()) {
			//There are no cells, just take trivially 0
			sample = RAN(0);
			return 0;
		}

		if (!cells.front().derivation->cell().lower_unbounded()) {
			//Lower bound is finite, just take a sufficiently large negative number
			sample = carl::sample_below(cells.front().derivation->cell().lower()->first);
			return 0;
		}

		if (!cells.back().derivation->cell().upper_unbounded()) {
			//Upper bound is finite, just take a sufficiently large positive number
			sample = carl::sample_above(cells.back().derivation->cell().upper()->first);
			return 0;
		}

		//Search for adjacent disjoint cells and sample between
		for (size_t i = 0; i + 1 < cells.size(); i++) {
			//We know that the cells are ordered by lower bound - so for checking disjointness the following suffices
			if (!cells[i].derivation->cell().upper_unbounded() && !cells[i+1].derivation->cell().lower_unbounded() && cells[i].derivation->cell().upper()->first < cells[i+1].derivation->cell().lower()->first) {
				sample = carl::sample_between(cells[i].derivation->cell().upper()->first, cells[i + 1].derivation->cell().lower()->first);
				return 0;

			//The check above does not care for open bounds
			//i.e if we have (x, y), (y, z) we can still choose y as a sample point
			} else if (cells[i].derivation->cell().is_sector() && cells[i + 1].derivation->cell().is_sector() && cells[i].derivation->cell().upper()->first == cells[i + 1].derivation->cell().lower()->first) {
				sample = cells[i].derivation->cell().upper()->first;
				return 0;
			}
		}


		//The cells cover the number line -> There is no sample to be found
		assert(is_valid());
		return 1 ;
	}

	bool isSampleOutside(const RAN& sample){
		SMTRAT_LOG_DEBUG("smtrat.covering", "Checking if sample " << sample << " is outside of: " << *this)
		if(cells.empty()){
			return true;
		}

		if (!cells.front().derivation->cell().lower_unbounded()) {
			//Lower bound is finite, checking if the sample is lower than the lower bound
			if(sample < cells.front().derivation->cell().lower()->first){
				return true;
			}
		}

		if (!cells.back().derivation->cell().upper_unbounded()) {
			//Upper bound is finite,checking if the sample is greater than the upper bound
			if(sample > cells.back().derivation->cell().upper()->first){
				return true;
			}
		}

		//Search for adjacent disjoint cells and sample between
		for (size_t i = 0; i + 1 < cells.size(); i++) {
			//We know that the cells are ordered by lower bound - so for checking disjointness the following suffices
			if (!cells[i].derivation->cell().upper_unbounded() && !cells[i+1].derivation->cell().lower_unbounded() && cells[i].derivation->cell().upper()->first < cells[i+1].derivation->cell().lower()->first) {
				if(cells[i].derivation->cell().upper()->first < sample && sample < cells[i + 1].derivation->cell().lower()->first){
					return true;
				}

			//The check above does not care for open bounds
			//i.e if we have (x, y), (y, z)
			} else if (cells[i].derivation->cell().is_sector() && cells[i + 1].derivation->cell().is_sector() && cells[i].derivation->cell().upper()->first == cells[i + 1].derivation->cell().lower()->first) {
				if(sample == cells[i].derivation->cell().upper()->first){
					return true;
				}
			}
		}

		return false ;
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
			if (std::prev(cell)->derivation->cell().upper()->first < cell->derivation->cell().lower()->first) return false;
			if (std::prev(cell)->derivation->cell().upper()->first == cell->derivation->cell().lower()->first && std::prev(cell)->derivation->cell().is_sector() && cell->derivation->cell().is_sector()) return false;
		}
		if (!cell->derivation->cell().upper_unbounded()) return false;

		// redundancy
		cell = cells.begin();
		while (cell != std::prev(cells.end())) {
			cell++;
			if (std::prev(cell)->derivation->cell().upper_unbounded()) return false;
			if (cell->derivation->cell().upper_unbounded()) continue;
			if (std::prev(cell)->derivation->cell().upper()->first > cell->derivation->cell().upper()->first) return false;
			if (std::prev(cell)->derivation->cell().upper()->first == cell->derivation->cell().upper()->first && std::prev(cell)->derivation->cell().is_sector() && cell->derivation->cell().is_sector()) return false;
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

	DelineationRepresentation(DelineatedDerivation<P>& deriv)
		: derivation(deriv) {}
};
template<typename P>
std::ostream& operator<<(std::ostream& os, const DelineationRepresentation<P>& data) {
	os << "(ordering: " << data.ordering << "; derivation: " << &data.derivation << ")";
	return os;
}

} // namespace smtrat::cadcells::datastructures