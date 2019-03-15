#pragma once

#include <carl/interval/Interval.h>
#include "../common.h"

#include "Sample.h"

namespace smtrat {
namespace cad {
	template<typename Settings>
	class LiftingLevel {
	public:
		using Interval = carl::Interval<RAN>;
	private:
		const ConstraintT& mConstraints;
		std::vector<carl::Variable> mVariables;
		Sample curSample;
		//std::vector<UPoly&> polynoms; @todo
		std::vector<Interval> intervals; 	// unsat intervals
		std::set<RAN> levelintervals;		// all bounds of unsat intervals, ordered
		bool levelintervalminf;				// whether -inf is a bound
		bool levelintervalpinf;				// whether +inf is a bound
		
		std::size_t dim() const {
			return mVariables.size();
		}

		void computeUnsatIntervals() {
			//@todo see alg 2
		}

		void addUnsatInterval(Interval& inter) {
			intervals.push_back(inter);

			// -inf or +inf are special cases
			if(inter.isInfinite()) {
				levelintervalminf = true;
				levelintervalpinf = true;
			}
			else if (inter.isHalfBounded())
			{
				// @todo how to find out which bound is inf
			}
			else {
				levelintervals.insert(inter.lower());
				levelintervals.insert(inter.upper());
			}
		}

		// @note check whether an unsat cover has been found before calling this
		Sample chooseSample() {
			std::set<RAN>::iterator it = levelintervals.begin();
			// go to the next bound (may equal last sample)
			while((*it) > curSample.value()) {
				it++;
			}

			//@todo special cases for -inf, +inf
			/*
			if(it == levelintervals.begin() && it.getLowerBoundType == BoundType::INFTY) {
				it++;
				if(it == levelintervals.end() && it.getUpperBoundType == BoundType::INFTY) {
					//@todo case levelintervals = {-inf, +inf}: get some random value in between
				}
			}
			else {

			} */

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

		LiftingLevel(){
			computeUnsatIntervals();
			//@todo: init intervals, levelintervals 
		}

		void reset(std::vector<carl::Variable>&& vars) {
			mVariables = std::move(vars);
			//@todo current sample
			intervals.clear();
			levelintervals.clear();
		}

		const auto& getUnsatIntervals() const {
			return intervals;
		}

		/** checks whether the unsat intervals contain (-inf, inf) */
		bool isSingletonCover() {
			if(intervals.empty()) {
				return false;
			}
			else {
				for(auto inter : intervals) {
					if(inter.isInfinite()) {
						return true;
					}
				}
			}
			return false;
		}

		bool isUnsatCover() {
			if(isSingletonCover()) {
				return true;
			}

			if(!levelintervalminf || !levelintervalpinf) {
				return false;
			}

			/* start with a (-inf, x) interval,
			 * find the next overlapping/joining interval and store upper bound,
			 * find next overlapping/joining interval for that bound with higher upper bound,
			 * continue until no overlapping interval or +inf found,
			 * if +inf is not found, there is no cover*/

			//@todo
		}

	};
}
};
