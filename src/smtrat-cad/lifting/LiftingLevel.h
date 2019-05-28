#pragma once

#include "../common.h"
#include "CADInterval.h"

#include <carl/interval/sampling.h>
#include <carl/interval/Interval.h>
#include <carl/core/rootfinder/RootFinder.h>

#include "Sample.h"

namespace smtrat {
namespace cad {
	template<typename Settings>
	class LiftingLevel {
	private:
		//@todo check which of these are used and that all are initialized
		std:vector<const ConstraintT&> mConstraints = std:vector<const ConstraintT&>();	/**< constraints */
		carl::Variable currVar						= carl::Variable();					/**< this level is considered univariate on given variable */
		std::vector<carl::Variable> mVariables 		= std::vector<carl::Variable>();	/**< variables */
		Sample curSample	 						= Sample();							/**< current sample to be checked */
		std::vector<CADInterval> intervals 			= std::vector<CADInterval>();		/**< unsat intervals */
		std::set<RAN> levelintervals 				= set<RAN>();						/**< all bounds of unsat intervals, ordered */
		bool levelintervalminf			 			= false;							/**< whether -inf is a bound */
		bool levelintervalpinf 						= false;							/**< whether +inf is a bound */
		
		//@todo check all fcnts and add doxygen conform comments

		/** gets the current dimension (#variables) */
		std::size_t dim() const {
			return mVariables.size();
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

		/** check whether the given value is in the list of unsat intervals */
		bool isInUnsatInterval(RAN val) {
			for(auto inter : intervals) {
				if(inter.contains(val)) {
					return true;
				}
			}
			return false;
		}

		/** 
		 * @brief Gives the lowest bound followed by an unexplored interval
		 * 
		 * Goes through the unsat intervals starting from -inf,
		 * if -inf is not a bound yet it is determined to be the first "upper" bound 
		 * to encode that there is an open interval smaller than any known bound.
		 * Else the first bound not followed by another unsat interval is returned.
		 * 
		 * @returns bool (first value of tuple) true iff a bound was found
		 * @returns RAN (second value of tuple) bound iff one was found, 0 otherwise
		 * @returns bool (third value of tuple) true iff the bound is open, otherwise it is closed
		 * @returns bool (fourth value of tuple) true iff -inf is is not a bound yet
		 * 
		 * @note The output (true, 0, false, true) stands for an unexplored
		 * interval before the first recorded bound
		 */
		std::tuple<bool, RAN, bool, bool> getLowestUpperBound() {
			// if (-inf, +inf) is included, return false
			if(isSingletonCover()) {
				return std::make_tuple(false, (RAN) 0, false, false);
			}
			// if -inf is no bound, there is some unexplored interval before the first recorded bound
			if(levelintervalminf == false) {
				return std::make_tuple(true, (RAN) 0, false, true);
			}

			// get an interval with -inf bound, store its higher bound
			RAN highestbound;
			bool boundopen;
			for(auto inter : intervals) {
				if(inter.getLowerBoundType() == CADInterval::CADBoundType::INF) {
					// note: the higher bound cannot be +inf as there is no singleton cover
					highestbound = inter.getUpper();
					boundopen = (inter.getUpperBoundType() == CADInterval::CADBoundType::OPEN) ? true : false;
					break;
				}
			}
			// iteratively check for highest reachable bound
			bool stop = false;
			while(!stop) {
				bool updated = false;
				for(auto inter : intervals) {
					updated = false;
					// if the upper bound is the highest bound but is included only update bound type
					if(highestbound == inter.getUpper() && inter.getUpperBoundType() == CADInterval::CADBoundType::CLOSED) {
						boundopen = false;
					}
					// update highest bound if the upper bound is not equal to the current highest bound,
					else if(!(highestbound == inter.getUpper() && 
						((boundopen && inter.getUpperBoundType() == CADInterval::CADBoundType::OPEN) || 
						 (!boundopen && inter.getUpperBoundType() == CADInterval::CADBoundType::CLOSED)))) {
						// and is contained in the interval or is bordered by the lower bound of the interval
						if(inter.contains(highestbound) ||
							(highestbound == inter.getLower() && 
							((boundopen && inter.getLowerBoundType() == CADInterval::CADBoundType::CLOSED) || 
								(!boundopen && inter.getLowerBoundType() == CADInterval::CADBoundType::OPEN)))) {
							if(inter.getUpperBoundType() == CADInterval::CADBoundType::INF) {
								// an unset cover was found
								return std::make_tuple(false, (RAN) 0, false, false);
							}
							// update to next higher bound
							highestbound = inter.getUpper();
							boundopen = (inter.getUpperBoundType() == CADInterval::CADBoundType::OPEN) ? true : false;
							updated = true;
						}
					}
				}
				// if the highest bound could not be updated (& was not +inf), break
				if(!updated) {
					stop = true;
				}
			}
			return std::make_tuple(true, highestbound, boundopen, false);
		}

		/**
		 * Calculates the intervals between the real roots of the given set of constraints
		 */
		void calcIntervalsFromPolys(Variable v, std::vector<const ConstraintT&> conss) {
			std::vector<RAN> roots;
			for (const auto& c: conss) {
				// find real roots of every constraint
				auto r = rootfinder::realRoots(c.lhs().toUnivariatePolynomial(v));
				r.sort(r.begin(), r.end()); // roots have to be ordered
				
				// go through roots to build intervals and add them to the lifting level
				std::vector<RAN>::iterator it;
				for (it = r.begin(); it != r.end(); it++) {
					// add closed point interval for each root
					addUnsatInterval(CADInterval(*it), c);

					// add inf intervals if appropriate
					if (it == r.begin()) // add (-inf, x)
						addUnsatInterval(CADInterval(0, *it, CADBoundType::INF, CADBoundType::OPEN, c));
					else if (it == r.back()) // add (x, inf)
						addUnsatInterval(CADInterval(*it, 0, CADBoundType::OPEN, CADBoundType::INF, c));
					
					// add open interval to next root
					if (it != r.back())
						addUnsatInterval(CADInterval(*it, *(std::next(it,1)), c));
				}
			}
		}

	public:

		//@todo init all class vars
		LiftingLevel(std:vector<const ConstraintT&> conss, carl::Variable v): 
			mConstraints(conss), currVar(v) {
			calcIntervalsFromPolys(currVar, mConstraints);
		}

		void reset(std::vector<carl::Variable>&& vars) {
			mVariables = std::move(vars);
			//@todo current sample
			intervals.clear();
			levelintervals.clear();
		}

		/** gets the current sample */
		const auto& getCurrentSample() const {
			return curSample;
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