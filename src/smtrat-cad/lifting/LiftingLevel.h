#pragma once


#include <carl/interval/Interval.h>
#include "../common.h"

namespace smtrat {
namespace cad {
	template<typename Settings>
	class LiftingLevel {
	public:
		using Interval = carl::Interval;
	private:
		const Constraints& mConstraints;
		std::vector<carl::Variable> mVariables;
		Sample curSample;
		std::vector<UPoly&> polynoms;
		std::vector<Interval> intervals; 	// unsat intervals
		std::set<RAN> levelintervals;		// all bounds of unsat intervals, ordered
        LiftingLevel predecessor;			//@todo or list of all levels somewhere.
		
		std::size_t dim() const {
			return mVariables.size();
		}

		void addInterval(Interval inter) {
			intervals.insert(inter);
			levelintervals.insert(inter.lower());
			levelintervals.insert(inter.upper());
		}

		// @note check whether an unsat cover has been found before calling this
		Sample chooseSample() {
			std::set<RAN>::iterator it = levelintervals.begin();
			// go to the next bound (may equal last sample)
			while(it->value > curSample) {
				it.next();
			}

			if(it == levelintervals.begin() && it.getLowerBoundType == BoundType::INFTY) {
				it.next();
				if(it == levelintervals.end() && it.getUpperBoundType == BoundType::INFTY) {
					//@todo case levelintervals = {-inf, +inf}: get some random value in between
				}
			}
			else {

			}

			//make sample here and check whether it is in some interval (isInUnsatInterval)
			// first sample before first bound (if bound is not minf), 
			//then on & between bounds, last one after last bound if not pinf 
		
			for(auto interval : intervals) {
				//@todo cases: minf, lower, equal, higher, pinf
				//
			}
		}

		// check whether the given value is in the list of unsat intervals
		bool isInUnsatInterval(RAN val) {
			for(auto inter : intervals) {
				if(inter.contains(val)) {
					return true;
				}
			}
			return false;
		}

	public:

		LiftingLevel(LiftingLevel& lev):predecessor{lev}{
			predecessor = lev;
			//@todo: init intervals, levelintervals 
		}

	};
}
}
