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

		Sample chooseSample() {
			std::set<RAN>::iterator it = levelintervals.begin();
			if(it.getLowerBoundType == BoundType::INFTY) {
				it.next();
			}

			//make sample here and check whether it is in some interval (open/closed!)
			// first sample before first bound (in bound is not minf), 
			//then between bounds, last one after last bound if not pinf 
		
			for(auto interval : intervals) {
				//@todo cases: minf, lower, equal, higher, pinf
				//
			}
		}

	public:

		LiftingLevel(LiftingLevel& lev):predecessor{lev}{
			predecessor = lev;
			//@todo: init intervals, levelintervals 
		}

	};
}
}
