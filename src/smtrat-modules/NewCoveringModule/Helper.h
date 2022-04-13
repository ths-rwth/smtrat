/**
 * @file Helper.h
 * @author Philip Kroll <Philip.Kroll@rwth-aachen.de>
 * Created on 2022-03-16.
 */
#pragma once

#include <smtrat-cadcells/datastructures/derivation.h>

namespace smtrat {

// We want to store the SampledDerivationRefs in a sorted datastructure (std::set), so we need to introduce a < operator for this.
// The derivations are sorted based on lower bounds of the respective cells, according to https://arxiv.org/pdf/2003.05633.pdf 4.4.1
struct SampledDerivationRefCompare {
	template<typename T>
	inline constexpr bool operator()(const cadcells::datastructures::SampledDerivationRef<T>& a, const cadcells::datastructures::SampledDerivationRef<T>& b) const {
		auto cell_a = a->cell();
		auto cell_b = b->cell();
		return cadcells::datastructures::lower_lt_lower(cell_a, cell_b) || (cadcells::datastructures::lower_eq_lower(cell_a, cell_b) && cadcells::datastructures::upper_lt_upper(cell_b, cell_a));
	}
};





} // namespace smtrat
