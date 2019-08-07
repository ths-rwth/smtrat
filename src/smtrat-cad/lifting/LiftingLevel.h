#pragma once

#include "../common.h"
#include "CADInterval.h"

#include <carl/interval/sampling.h>
#include <carl/interval/Interval.h>
#include <carl/core/rootfinder/RootFinder.h>
#include <carl/util/Common.h>

#include "Sample.h"

namespace smtrat {
namespace cad {
	template<typename Settings>
	class LiftingLevel {
	private:
		//@todo check which of these are used and that all are initialized
		std::vector<ConstraintT> mConstraints = std::vector<ConstraintT>();				/**< constraints */
		carl::Variable currVar						= carl::Variable();					/**< this level is considered univariate on given variable */
		std::vector<carl::Variable> mVariables 		= std::vector<carl::Variable>();	/**< variables, ordered */
		Sample curSample	 						= Sample();							/**< current sample to be checked */
		std::vector<CADInterval> intervals 			= std::vector<CADInterval>();		/**< unsat intervals */
		std::set<RAN> levelintervals 				= set<RAN>();						/**< all bounds of unsat intervals, ordered */
		bool levelintervalminf			 			= false;							/**< whether -inf is a bound */
		bool levelintervalpinf 						= false;							/**< whether +inf is a bound */
		
		//@todo check all fcnts and add doxygen conform comments

		/** gets the current dimension (#variables)
		 * @returns current dimension
		 */
		std::size_t dim() const {
			return mVariables.size();
		}

		/** check whether the given value is in the list of unsat intervals
		 * @returns true if value is in unsat interval
		 */
		bool isInUnsatInterval(RAN val) {
			for(auto inter : intervals) {
				if(inter.contains(val)) {
					return true;
				}
			}
			return false;
		}


		/** adds an unsat interval to the internal data structures of the level */
		void addUnsatInterval(CADInterval inter) {
			intervals.push_back(inter);

			// -inf or +inf are special cases
			if(inter.isInfinite()) {
				levelintervalminf = true;
				levelintervalpinf = true;
			}
			else if(inter.isHalfBounded())
			{
				if(inter.getLowerBoundType() == CADInterval::CADBoundType::INF) {
					levelintervalminf = true;
					levelintervals.insert(inter.getUpper());
				}
				else {
					levelintervalpinf = true;
					levelintervals.insert(inter.getLower());
				}
			}
			else {
				levelintervals.insert(inter.getLower());
				levelintervals.insert(inter.getUpper());
			}
		}

	public:

		//@todo init all class vars
		LiftingLevel(std::vector<ConstraintT> conss, carl::Variable v): 
			mConstraints(conss), currVar(v) {
			addUnsatIntervals(calcIntervalsFromPolys(currVar, mConstraints));
		}

		void reset(std::vector<carl::Variable>&& vars) {
			mVariables = std::move(vars);
			//@todo current sample
			resetIntervals();
		}

		/** removes all stored intervals */
		void resetIntervals() {
			intervals.clear();
			levelintervals.clear();
			levelintervalminf = false;
			levelintervalpinf = false;
		}

		/** gets the current sample */
		const auto& getCurrentSample() const {
			return curSample;
		}


		/** adds a set of unsat intervals */
		void addUnsatIntervals(std::set<CADInterval> inters) {
			for(auto inter : inters) {
				addUnsatInterval(inter);
			}
		}


		/** @brief Checks whether an unsat cover was found
		 * 
		 * Checks whether the detected unsat intervals cover the reals in this level with given prefix
		 * @returns true iff there is an unsat cover
		 */
		bool isUnsatCover() {
			// check whether -inf and +inf are included
			if(!levelintervalminf || !levelintervalpinf) {
				return false;
			}
			if(isSingletonCover()) {
				return true;
			}
			
			// check whether any unexplored interval remains
			auto boundtuple = getLowestUpperBound();
			if (!std::get<0>(boundtuple)) {
				return true;
			}
			return false;
		}


		/** @brief computes the next Sample
		 * 
		 * Chooses a Sample outside the currently known unsat intervals
		 * 
		 * @note check whether an unsat cover has been found before calling this
		 * @todo when using infty bounds in carl intervals, is 0 a valid bound input?
		 */
		Sample chooseSample() {
			//@todo remove the current value of curSample

			// if -inf is not a bound find sample in (-inf, first bound)
			if(!levelintervalminf) {
				RAN upper = levelintervals.begin();
				auto computeinterval = carl::Interval<RAN>(0, carl::BoundType::INFTY, upper, carl::BoundType::STRICT);
				RAN samplenr = sample(computeinterval, false); 
				curSample = Sample(samplenr);
			}

			auto boundtuple = getLowestUpperBound();
			assert(std::get<0>(boundtuple)); //@todo handle this instead
			RAN bound = std::get<1>(boundtuple);

			// check whether the nex unexplored interval is a point interval
			for(auto inter: intervals) {
				if(bound == inter.getLower() && inter.getLowerBoundType() == CADInterval::CADBoundType::OPEN 
					&& !isInUnsatInterval(bound)) {
					curSample = Sample(bound); //@todo is this a root in this case? if so, set isRoot of sample
				}
			}

			// case the next lowest upper bound is the last recorded bound
			if(bound == *levelintervals.rbegin()) {
				auto computeinterval = carl::Interval<RAN>(bound, carl::BoundType::STRICT, 0, carl::BoundType::INFTY);
				RAN samplenr = sample(computeinterval, false); 
				curSample = Sample(samplenr);
			}

			// go to the next bound
			//@todo assuming that set is ordered. check that
			std::set<RAN>::iterator it = levelintervals.begin();
			while((*it) < std::get<1>(boundtuple)) {
				it++;
			}
			// determine whether next bound is closed, do not break in case bound appears > once.
			bool boundopen = true;
			for(auto bound : intervals) {
				if(bound.getLower() == (*it)) {
					if(bound.getLowerBoundType() == CADInterval::CADBoundType::CLOSED) {
						boundopen = false;
					}
				}
			}
			// we got the bounds and their types, find sample in between
			auto computeinterval = carl::Interval<RAN>(std::get<1>(boundtuple),(*it)); //@todo bound types?
			RAN samplenr = sample(computeinterval, false); 
			//@todo the false leads to bounds not included, so we prefer choosing samples that are not bounds. is that important?
			curSample = Sample(samplenr);

			return curSample;
		}
	};
}
};