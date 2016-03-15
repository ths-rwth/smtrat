#pragma once

#include <algorithm>
#include <list>
#include <utility>
#include <vector>

#include "../Common.h"

#include "BaseProjection.h"

namespace smtrat {
namespace cad {
	
	template<Incrementality incrementality, Backtracking backtracking, typename Settings>
	class Projection: public BaseProjection {
	public:
		// Add a new constraint to the projection.
		void addPolynomial(const UPoly& p, std::size_t origin) {}
		// Remove an existing constraint from the projection.
		void removePolynomial(const UPoly& p, std::size_t origin, const std::function<void(std::size_t,SampleLiftedWith)>& callback) {}
		
		bool projectNewPolynomial(std::size_t level, const ConstraintSelection& ps = Bitset(true)) {}
		
		// Retrieve a polynomial to lift with.
		OptionalPoly getPolyForLifting(std::size_t level, const SampleLiftedWith& slw, const ConstraintSelection& cs = Bitset(true)) {}
		// Clean the lifted with parameter from removed polynomials.
		void cleanLiftedWith(std::size_t level, SampleLiftedWith& slw) const {}
	};
	
	template<typename Settings>
	using ProjectionT = Projection<Settings::incrementality, Settings::backtracking, Settings>;
}
}

#include "Projection_NO.h"
#include "Projection_NU.h"
#include "Projection_SO.h"
