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
		void addPolynomial(const UPoly& p) {}
		// Remove an existing constraint from the projection.
		void removePolynomial(const UPoly& p) {}
		
		bool projectNewPolynomial(std::size_t level, const ConstraintSelection& ps = Bitset(true)) {}
		
		// Retrieve a polynomial to lift with.
		OptionalPoly getPolyForLifting(std::size_t level, const SampleLiftedWith& slw, const ConstraintSelection& cs = Bitset(true)) {}
		// Clean the lifted with parameter from removed polynomials.
		void cleanLiftedWith(std::size_t level, SampleLiftedWith& slw) const {}
	};
	
	
	template<Backtracking backtracking, typename Settings>
	class Projection<Incrementality::SIMPLE, backtracking, Settings>: public BaseProjection {
	private:
		std::list<UPoly> mQueue;
	public:
		void addPolynomial(const UPoly& p) {
			mQueue.push_back(p);
		}
		void removePolynomial(const UPoly& p) {
			auto it = std::find(mQueue.begin(), mQueue.end(), p);
			if (it != mQueue.end()) {
				mQueue.erase(it);
			} else {
				// Erase from projection
			}
		}
	};
	
	template<typename Settings>
	using ProjectionT = Projection<Settings::incrementality, Settings::backtracking, Settings>;
}
}

#include "Projection_NO.h"
