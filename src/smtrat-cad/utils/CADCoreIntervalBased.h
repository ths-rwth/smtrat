#pragma once

#include "../common.h"
#include "../Settings.h"

#include <smtrat-cad/lifting/Sample.h>
#include <smtrat-cad/lifting/CADInterval.h>
// @todo #include <smtrat-cad/lifting/LiftingLevel.h>

#include <carl/core/rootfinder/RootFinder.h>

namespace smtrat {
namespace cad {

template<CoreIntervalBasedHeuristic CH>
struct CADCoreIntervalBased {};

template<>
struct CADCoreIntervalBased<CoreIntervalBasedHeuristic::UnsatCover> {
	// template<typename CADIntervalBased>
	// bool doProjection(CADIntervalBased& cad) {
	// 	auto r = cad.mProjection.projectNewPolynomial();
	// 	if (r.none()) {
	// 		SMTRAT_LOG_INFO("smtrat.cad", "Projection has finished.");
	// 		return false;
	// 	}
	// 	SMTRAT_LOG_INFO("smtrat.cad", "Projected into " << r << ", new projection is" << std::endl << cad.mProjection);
	// 	return true;
	// }
	// template<typename CADIntervalBased>
	// bool doLifting(CADIntervalBased& cad) {
	// 	//@todo is mLifting.back() applicable here? maybe specify lifting level or iterator instead for recursion
    //     // no lifting is possible if an unsat cover was found
	// 	if (cad.mLifting.back().isUnsatCover()) return false;

    //     while(!cad.mLifting.back().isUnsatCover()) {
    //         // compute a new sample outside of known unsat intervals
    //         auto s = cad.mLifting.back().chooseSample();
    //         SMTRAT_LOG_TRACE("smtrat.cad", "Next sample" << std::endl << s);
    //         //@todo check whether all former levels + new sample are sat, if true return sat

    //         auto intervals = cad.mLifting.getUnsatIntervals();
	// 	    SMTRAT_LOG_TRACE("smtrat.cad", "Current intervals" << std::endl << intervals);
    //     }

    //     //@todo this is code from CADCore, adapt
	// 	/*assert(0 <= it.depth() && it.depth() < cad.dim());
	// 	SMTRAT_LOG_DEBUG("smtrat.cad", "Processing " << cad.mLifting.extractSampleMap(it));
	// 	if (it.depth() > 0 && cad.checkPartialSample(it, cad.idLP(it.depth())) == Answer::UNSAT) {
	// 		cad.mLifting.removeNextSample();
	// 		return false;
	// 	}
	// 	auto polyID = cad.mProjection.getPolyForLifting(cad.idLP(it.depth() + 1), s.liftedWith());
	// 	if (polyID) {
	// 		const auto& poly = cad.mProjection.getPolynomialById(cad.idLP(it.depth() + 1), *polyID);
	// 		SMTRAT_LOG_DEBUG("smtrat.cad", "Lifting " << cad.mLifting.extractSampleMap(it) << " with " << poly);
	// 		cad.mLifting.liftSample(it, poly, *polyID);
	// 	} else {
	// 		SMTRAT_LOG_DEBUG("smtrat.cad", "Current lifting" << std::endl << cad.mLifting.getTree());
	// 		SMTRAT_LOG_TRACE("smtrat.cad", "Queue" << std::endl << cad.mLifting.getLiftingQueue());
	// 		cad.mLifting.removeNextSample();
	// 		cad.mLifting.addTrivialSample(it);
	// 	} */
	// 	return true;
	// }


	/** @brief checks whether the first variable is at least as high in the var order as the second one 
	 * 
	 * @returns true iff the first var is at least as high in the var order as the second one
	*/
	template<typename CADIntervalBased>
	bool isAtLeastCurrVar(
		CADIntervalBased& cad,	/**< corresponding CAD */
		carl::Variable v, 		/**< variable to check */
		carl::Variable currVar	/**< current variable */
	) {
		if(cad.getDepthOfVar(v) >= cad.getDepthOfVar(currVar))
			return true;

		return false;
	}


	/**
	 * Calculates the regions between the real roots of the polynom (left-hand side) of given constraint
	 * @param samples variables to be substituted by given values, can be empty
	 * @param currVar variable of current level
	 * 
	 * @returns set of intervals ordered by lower bounds, ascending
	 * 
	 * (Paper Alg. 1, l.9-11)
	 */
	template<typename CADIntervalBased>
	std::set<CADInterval> calcRegionsFromPoly(
		CADIntervalBased& cad,					/**< corresponding CAD */
		ConstraintT c, 							/**< constraint containing the polynom */
		std::map<carl::Variable, RAN> samples,	/**< variables to be substituted by given values, may be empty */
		carl::Variable currVar					/**< constraint is considered as univariate in this variable */
	) {
		std::set<CADInterval> regions;

		// find real roots of constraint corresponding to current var
		auto r = carl::rootfinder::realRoots(c.lhs().toUnivariatePolynomial(currVar), samples);
		std::sort(r.begin(), r.end());
		
		// go through roots to build region intervals and add them to the lifting level
		std::vector<RAN>::iterator it;
		for (it = r.begin(); it != r.end(); it++) {
			// add closed point interval for each root
			regions.insert( CADInterval(*it, c) );

			// add (-inf, x) for first root x
			if (it == r.begin())
				regions.insert( CADInterval((RAN) 0, *it, CADInterval::CADBoundType::INF, CADInterval::CADBoundType::OPEN, c) );
			
			// for last root x add (x, inf)
			if (it == r.rbegin().base())
				regions.insert( CADInterval(*it, (RAN) 0, CADInterval::CADBoundType::OPEN, CADInterval::CADBoundType::INF, c) );
			else // add open interval to next root
				regions.insert(CADInterval(*it, *(std::next(it, 1)), c) );
		}

		/* sort intervals by ascending order of lower bounds */
		std::sort(regions.begin(), regions.end(), [](CADInterval a, CADInterval b) {
			return a.isLowerThan(b);
		});

		return regions;
	}

	/** converts a std::map<carl::Variable, RAN> to EvalRationalMap
	 * as different carl classes need the same information in different format
	 */
	template<typename CADIntervalBased>
	 EvalRationalMap makeEvalMap( 
		 CADIntervalBased& cad,						/**< corresponding CAD */ 
		 const std::map<carl::Variable, RAN>& orig	/**< map to convert */
	) {
		// convert eval map to usable format
		EvalRationalMap map;
		for(auto entry : orig) {
			std::pair<carl::Variable, Rational> newentry = std::make_pair(entry.first, entry.second.value());
			map.insert(newentry);
		}
		return map;
	}


	/** @brief gets unsat intervals for depth i corresponding to given sample map
	 * 
	 * @returns unsat intervals ordered by lower bound, ascending
	 * 
	 * (Paper Alg. 1)
	*/
	template<typename CADIntervalBased>
	const std::set<CADInterval*>& get_unsat_intervals(
		CADIntervalBased& cad,					/**< corresponding CAD */ 
		std::map<carl::Variable, RAN> samples,	/**< values for variables of depth till i-1 (only used if dimension is > 1) */
		carl::Variable currVar					/**< variable of current depth i */
	) const {

		// @todo this checks all vars, not just main vars
		/* constraints are filtered for ones with main var currVar or higher */
		std::vector<ConstraintT> constraints;
		for(auto c : cad.mConstraints) {
			auto consvars = c.variables();
			for(auto v : consvars) {
				if(isAtLeastCurrVar(v, currVar)) {
					constraints.push_back(c);
					break;
				}
			}
		}

		/* gather intervals from each constraint */
		std::set<CADInterval*> newintervals;
		for(auto c : constraints) {
			unsigned issat = c.satisfiedBy(makeEvalMap(cad, samples));
			/* if unsat, return (-inf, +inf) */
			if(issat == 0) { /*@todo is this equiv to "c(s) == false"? */
				std::set<CADInterval*> set;
				set.insert(new CADInterval(c));
				return set;
			}
			/* if sat, constraint is finished */
			else if(issat == 1)
				continue;
			else { /* @todo this should be the satisfiedBy result with open vars */
				// get unsat intervals for constraint
				auto regions = calcRegionsFromPoly(cad, c, samples, currVar);
				for(auto region : regions) {
					auto r = region.getRepresentative();
					std::map<carl::Variable, RAN> eval = new std::map<carl::Variable, RAN>(samples);
					eval.insert(std::pair<carl::Variable, RAN>(currVar, r));
					std::vector<Poly> lowerreason;
					std::vector<Poly> upperreason;
					if(c.satisfiedBy(makeEvalMap(cad, eval)) == 0) { //@todo again, is this right?
						if(region.getLowerBoundType() != CADInterval::CADBoundType::INF)
							lowerreason.push_back(c.lhs());
						if(region.getUpperBoundType() != CADInterval::CADBoundType::INF)
							upperreason.push_back(c.lhs());
						newintervals.insert(new CADInterval(region.getLower(), region.getUpper(), region.getLowerBoundType(), region.getUpperBoundType(), lowerreason, upperreason, c));
					}
				} 
			}
		}

		/* sort intervals by ascending order of lower bounds */
		std::sort(newintervals.begin(), newintervals.end(), [](CADInterval* a, CADInterval* b) {
			return (*a).isLowerThan(*b);
		});

		return newintervals;
	}


	/** 
	 * @brief Gives the lowest bound followed by an unexplored region
	 * 
	 * Goes through the unsat intervals starting from -inf,
	 * if -inf is not a bound yet it is determined to be the first "upper" bound.
	 * Else the first bound not followed by another interval is returned.
	 * 
	 * @returns bool 				(1st value of tuple) true iff a bound was found
	 * @returns RAN  				(2nd value of tuple) bound iff one was found, 0 otherwise
	 * @returns CADBoundType 		(3rd value of tuple) type of bound if one was found or OPEN if none was found (if this is INF, the found "bound" is -inf)
	 * @returns set<CADInterval> 	(4th value of tuple) contains intervals of covering iff no bound was found, else empty
	 * 
	 * @note The output (true, 0, INF, emptyset) stands for an unexplored interval before the first given interval
	 */
	template<typename CADIntervalBased>
	std::tuple<bool, RAN, CADInterval::CADBoundType, std::set<CADInterval*>> getLowestUpperBound(
		CADIntervalBased& cad,				/**< corresponding CAD */
		std::set<CADInterval*> intervals	/**< set of intervals to be checked for unexplored regions */
	) {
		// check whether there are intervals
		if(intervals.empty()) {
			auto tuple = std::make_tuple(false, (RAN) 0, CADInterval::CADBoundType::OPEN, std::set<CADInterval*>());
			return tuple;
		}

		// check for (-inf, +inf) interval
		for(auto inter : intervals) {
			if(inter->isInfinite()) {
				auto infset = std::set<CADInterval*>();
				infset.insert(inter);
				auto tuple = std::make_tuple(false, (RAN) 0, CADInterval::CADBoundType::OPEN, infset);
			}
		}

		std::set<CADInterval*> cover;

		// get an interval with -inf bound, store its higher bound
		RAN highestbound = (RAN) 0;
		CADInterval::CADBoundType boundopen = CADInterval::CADBoundType::OPEN;
		bool hasminf = false;
		for(auto inter : intervals) {
			// check for singleton cover
			if(inter->isInfinite()) {
				auto infset = std::set<CADInterval*>();
				infset.insert(inter);
				auto tuple = std::make_tuple(false, (RAN) 0, CADInterval::CADBoundType::OPEN, infset);
				return tuple;
			}
			if(inter->getLowerBoundType() == CADInterval::CADBoundType::INF) {
				// note: the higher bound cannot be +inf as there is singleton cover was checked before
				highestbound = inter->getUpper();
				boundopen = inter->getUpperBoundType();
				cover.insert(inter);
				hasminf = true;
				break;
			}
		}
		// if -inf is no bound in any interval, there is some unexplored region before the first interval
		if(!hasminf) {
			auto tuple = std::make_tuple(true, (RAN) 0, CADInterval::CADBoundType::INF, std::set<CADInterval*>());
			return tuple;
		}

		// iteratively check for highest reachable bound
		bool stop = false;
		while(!stop) {
			bool updated = false;
			for(auto inter : intervals) {
				updated = false;
				// if the upper bound is the highest bound but is included only update bound type
				if(highestbound == inter->getUpper() && boundopen == CADInterval::CADBoundType::OPEN && inter->getUpperBoundType() == CADInterval::CADBoundType::CLOSED) {
					boundopen = inter->getUpperBoundType();
					cover.insert(inter);
					updated = true;
				}
				// update if the upper bound is not equal to highestbound 
				// note: checking (highestbound < upper bound) would ommit (upper bound == INF) case
				else if( !(highestbound == inter->getUpper() && boundopen == inter->getUpperBoundType()) ) {
					// and if highestbound is contained in the interval or is bordered by the lower bound of the interval
					// (also excludes the case upper bound < highestbound)
					assert(boundopen != CADInterval::CADBoundType::INF);
					if(inter->contains(highestbound) ||
						(highestbound == inter->getLower() && boundopen != inter->getLowerBoundType() && 
						inter->getLowerBoundType() != CADInterval::CADBoundType::INF)) {
						
						cover.insert(inter);
						if(inter->getUpperBoundType() == CADInterval::CADBoundType::INF) {
							// an unset cover was found
							auto tuple = std::make_tuple(false, (RAN) 0, CADInterval::CADBoundType::OPEN, cover);
							return tuple;
						}
						// update to next higher bound
						highestbound = inter->getUpper();
						boundopen = inter->getUpperBoundType();
						updated = true;
					}
				}
			}
			// if the highest bound could not be updated (& was not +inf), break
			if(!updated) {
				stop = true;
			}
		}
		
		auto tuple = std::make_tuple(true, highestbound, boundopen, std::set<CADInterval*>());
		return tuple;
	}


	/**@brief computes a cover from the given set of intervals
	 * 
	 * @returns subset of intervals that form a cover or an empty set if none was found
	 * (Paper Alg. 2)
	 */
	template<typename CADIntervalBased>
	std::set<CADInterval>compute_cover(
		CADIntervalBased& cad, 			/**< corresponding CAD */
		std::set<CADInterval*> inters	/**< set of intervals over which to find a cover */
	) {
		// return cover or empty set if none was found
		auto boundtuple = getLowestUpperBound(cad, inters);
		return std::get<3>(boundtuple);
	}

	/** @brief computes the next sample
	 * 
	 * Chooses a Sample outside the currently known unsat intervals
	 * 
	 * @returns RAN in unexplored interval
	 * @note check whether an unsat cover has been found before calling this!
	 */
	template<typename CADIntervalBased>
	RAN chooseSample(
		CADIntervalBased& cad,			/**< corresponding CAD */
		std::set<CADInterval*> inters	/**< known unsat intervals */
	) {
		// if -inf is not a bound find sample in (-inf, first bound)
		bool hasminf = false;
		bool first = true;
		RAN lowestval = 0;
		for(auto inter : inters) {
			if(inter->getLowerBoundType() == CADInterval::CADBoundType::INF) {
				hasminf = true;
				break;
			}
			else {
				// get lowest bound
				if(first) {
					lowestval = inter->getLower();
					first = false;
				}
				else {
					if(inter->getLower() < lowestval)
						lowestval = inter->getLower();
				}
			}
		}
		// if no -inf bound, get val below
		if(!hasminf) {
			return sampleBelow(lowestval);
		}

		// get first unexplored region
		auto boundtuple = getLowestUpperBound(cad, inters);
		assert(std::get<0>(boundtuple)); //@todo handle this instead
		RAN bound = std::get<1>(boundtuple);
		// note: at this point the bound is not -inf (case is handled above)

		// get lower bound of next interval after the unexplored region iff one exists
		bool found = false;
		RAN upperbound;
		CADInterval::CADBoundType upperboundtype;
		for(auto inter : inters) {
			if(bound < inter->getLower() && inter->getLowerBoundType() != CADInterval::CADBoundType::INF) {
				found = true;
				upperbound = inter->getLower();
				upperboundtype = inter->getLowerBoundType();
			}
			// case bound == inter.lower can only happen if found == true, initially was covered by getLowestUpperBound
			else if(bound == inter->getLower() && upperboundtype == CADInterval::CADBoundType::OPEN 
				&& inter->getLowerBoundType() == CADInterval::CADBoundType::CLOSED) {
				upperboundtype == CADInterval::CADBoundType::CLOSED;
			}
		}
		// if none was found, next bound is +inf
		if(!found) {
			upperboundtype = CADInterval::CADBoundType::INF;
			upperbound = (RAN) 0;
		}

		// create interval in which to find the next sample
		CADInterval* sampleinterval = new CADInterval(bound, upperbound, std::get<2>(boundtuple), upperboundtype);
		return sampleinterval->getRepresentative();
	}

	template<typename CADIntervalBased>
	smtrat::Poly construct_characterization(
		CADIntervalBased& cad,					/**< corresponding CAD */
		std::map<carl::Variable, RAN> samples,	/**< values for variables till depth i */
		std::vector<CADInterval*> intervals		/**< intervals */
	) {
		//@todo
	}

	template<typename CADIntervalBased>
	CADInterval* interval_from_characterization(
		CADIntervalBased& cad,					/**< corresponding CAD */
	 	std::map<carl::Variable, RAN> samples,	/**< values for variables till depth i-1 */
		carl::Variable currVar,					/**< var of depth i (current depth) */
		RAN val, 								/**< value for currVar */
		smtrat::Poly butler						/**< poly characterization */
	) {
		//@todo
	}

	/**
	 * computes whether an unsat cover can be found or whether there is a satisfying witness
	 * 
	 * @returns true if SAT, false if UNSAT
	 * @returns in UNSAT case: intervals forming the unsat cover
	 * @returns in SAT case: satisfying witness
	 * 
	 * (Paper Alg. 3)
	 */
	template<typename CADIntervalBased>
	std::tuple<bool, std::vector<CADInterval*>, std::map<carl::Variable, RAN>> get_unsat_cover(
		CADIntervalBased& cad,					/**< corresponding CAD */
		std::map<carl::Variable, RAN> samples,	/**< values for variables of depth i-1 (initially empty set) */
		carl::Variable currVar					/**< var of depth i (current depth) */
	) {
		// get known unsat intervals
		std::vector<CADInterval*>& unsatinters = get_unsat_intervals(cad, samples);

		// run until a cover was found
		while(compute_cover(cad, unsatinters).empty()) {
			// add new sample for current variable
			std::map<carl::Variable, RAN> newsamples = new std::map<carl::Variable, RAN>(samples);
			RAN newval = chooseSample(cad, unsatinters);
			SMTRAT_LOG_TRACE("smtrat.cad", "Next sample " << std::endl << newval);
			newsamples.insert(std::make_pair(currVar, newval));

			// if the sample set has full dimension we have a satifying witness
			if(cad.dim() == cad.getDepthOfVar(currVar))
				return std::make_tuple(true, std::vector<CADInterval*>(), newsamples);

			// recursive recall for next dimension
			auto nextcall = get_unsat_cover(cad, newsamples, cad.getNextVar(currVar));
			// if SAT
			if(std::get<0>(nextcall))
				return nextcall;
			else {
				smtrat::Poly butler = construct_characterization(cad, newsamples, std::get<1>(nextcall));
				CADInterval* butlerinter = interval_from_characterization(cad, samples, currVar, newval, butler);
				unsatinters.push_back(butlerinter);
			}
		}

		// in case the loop exits a cover was found
		auto res = std::make_tuple(false, unsatinters, std::map<carl::Variable, RAN>());
		return res;
	}


	template<typename CADIntervalBased>
	Answer operator()(Assignment& assignment, CADIntervalBased& cad) {
        //@todo there should probably be a different preference order here?!
		cad.mLifting.restoreRemovedSamples();
		cad.mLifting.resetFullSamples();
		while (true) {
			Answer res = cad.checkFullSamples(assignment);
			if (res == Answer::SAT) return Answer::SAT;
			if (!cad.mLifting.hasNextSample()) {
				if (!doProjection(cad)) return Answer::UNSAT;
				cad.mLifting.restoreRemovedSamples();
			}
			if (preferLifting(cad.mLifting.getNextSample())) {
				doLifting(cad);
			} else {
				doProjection(cad);
				cad.mLifting.restoreRemovedSamples();
			}
		}
	}
};

}
}
