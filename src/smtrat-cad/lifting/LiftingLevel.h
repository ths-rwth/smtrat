#pragma once

#include "../common.h"
#include "CADInterval.h"

#include "Sample.h"

namespace smtrat {
namespace cad {
	template<typename Settings>
	class LiftingLevel {
	private:
		const ConstraintT& mConstraints;
		std::vector<carl::Variable> mVariables;
		Sample curSample;
		std::vector<CADInterval> intervals;	/**< unsat intervals */
		std::set<RAN> levelintervals;		/**< all bounds of unsat intervals, ordered */
		bool levelintervalminf;				/**< whether -inf is a bound */
		bool levelintervalpinf;				/**< whether +inf is a bound */
		
		//@todo check all fcnts and add doxygen conform comments

		std::size_t dim() const {
			return mVariables.size();
		}

		void computeUnsatIntervals() {
			//@todo see alg 2
		}

		/** adds an unsat interval to the internal data structures of the level */
		void addUnsatInterval(Interval& inter) {
			intervals.push_back(inter);

			// -inf or +inf are special cases
			if(inter.isInfinite()) {
				levelintervalminf = true;
				levelintervalpinf = true;
			}
			else if(inter.isHalfBounded())
			{
				if(inter.getLowerBoundType() == CADBoundType::INF) {
					levelintervalminf = true;
					levelintervals.insert(inter.upper());
				}
				else {
					levelintervalpinf = true;
					levelintervals.insert(inter.lower());
				}
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

		/** gets all unsat intervals */
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

		/** check whether an unsat cover was found */
		bool isUnsatCover() {
			// check whether -inf and +inf are included
			if(!levelintervalminf || !levelintervalpinf) {
				return false;
			}
			if(isSingletonCover()) {
				return true;
			}
			
			// get an interval with -inf bound, store its higher bound
			int highestbound;
			bool boundopen;
			for(auto inter : intervals) {
				if(inter.getLowerBoundType() == CADBoundType::INF) {
					// note: the higher bound cannot be +inf as there is no singleton cover
					highestbound = inter.upper();
					boundopen = (inter.getUpperBoundType() == CADBoundType::OPEN) ? true : false;
					break;
				}
			}
			// iteratively check for highest reachable bound
			bool stop = false;
			while(!stop) {
				for(auto inter : intervals) {
					bool updated = false;
					// update highest bound if the upper bound is not equal to the current highest bound,
					if(!(highestbound == inter.upper() && 
						((boundopen && inter.getUpperBoundType() == CADBoundType::OPEN) || 
						 (!boundopen && inter.getUpperBoundType() == CADBoundType::CLOSED)))) {
						// and is contained in the interval or is bordered by the lower bound of the interval
						if(inter.contains(highestbound) ||
							(highestbound == inter.lower && 
							((boundopen && inter.getLowerBoundType() == CADBoundType::CLOSED) || 
								(!boundopen && inter.getLowerBoundType() == CADBoundType::OPEN)))) {
							if(inter.getUpperBoundType() == CADBoundType::INF) {
								return true;
							}
							highestbound = inter.upper();
							boundopen = (inter.getUpperBoundType() == CADBoundType::OPEN) ? true : false;
							updated = true;
						}
					}
				}
				// if the highest bound could not be updated (& was not +inf), no cover was found
				if(!updated) {
					stop = true;
				}
			}
			return false;
		}

	};
}
};
