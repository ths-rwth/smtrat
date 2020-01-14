#pragma once

#include "../common.h"
#include "../Settings.h"

#include <smtrat-cad/lifting/Sample.h>
#include <smtrat-cad/lifting/CADInterval.h>
// @todo #include <smtrat-cad/lifting/LiftingLevel.h>

#include <carl/core/polynomialfunctions/RootFinder.h>
#include <carl-model/Model.h>
#include <carl-model/evaluation/ModelEvaluation.h>

namespace smtrat {
namespace cad {

template<CoreIntervalBasedHeuristic CH>
struct CADCoreIntervalBased {};

template<>
struct CADCoreIntervalBased<CoreIntervalBasedHeuristic::UnsatCover> {

	/** custom sort for sets of CADIntervals */
	struct SortByLowerBound
	{
		bool operator ()(CADInterval* a, CADInterval* b) const {
			return a->isLowerThan(*b);
		}
	};


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

	void remove_duplicates(std::vector<ConstraintT>& c) {
		std::sort(c.begin(), c.end());
		c.erase(std::unique(c.begin(), c.end()), c.end());
	}

	void insert_factorized(std::set<Poly>& set, const Poly& p) {
		for (const auto& f: carl::irreducibleFactors(p, false)) {
			set.insert(f);
		}
	}


	/** @brief gets highest var in var order that is present in the polynom
	 * 
	 * with respect to variable order in cad
	 * 
	 * @returns highest var in polynom
	*/
	template<typename CADIntervalBased>
	carl::Variable getHighestVar(
		CADIntervalBased& cad,	/**< corresponding CAD */
		const smtrat::Poly& poly		/**< polynom */
	) {
		carl::Variable var;
		for(auto v : carl::variables(poly).underlyingVariables()) {
			if(cad.getDepthOfVar(v) > cad.getDepthOfVar(var)) 
				var = v;
		}
		return var;
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
	std::set<CADInterval*, SortByLowerBound> calcRegionsFromPoly(
		CADIntervalBased& cad,		/**< corresponding CAD */
		const ConstraintT& c, 				/**< constraint containing the polynom */
		const Assignment& samples,			/**< variables to be substituted by given values, may be empty */
		carl::Variable currVar		/**< constraint is considered as univariate in this variable */
	) {
		std::set<CADInterval*, SortByLowerBound> regions;

		carl::carlVariables vars = carl::variables(c.lhs());
		vars.erase(currVar);
		for (const auto& s: samples) vars.erase(s.first);
		if (!vars.empty()) {
			SMTRAT_LOG_INFO("smtrat.cdcad", c << " is not univariate in " << currVar << " over " << samples);
			return regions;
		}

		// find real roots of constraint corresponding to current var
		auto r = carl::rootfinder::realRoots(carl::to_univariate_polynomial(c.lhs(), currVar), samples);

		std::sort(r.begin(), r.end());

		// if there is no real root, there is just one interval: (-inf, +inf)
		if(r.empty()) {
			SMTRAT_LOG_INFO("smtrat.cdcad", "Roots of " << c << " do not exists");
			regions.insert( new CADInterval(c));
			return regions;
		}

		SMTRAT_LOG_TRACE("smtrat.cdcad", "Roots of " << c << ": " << r);
		
		// go through roots to build region intervals and add them to the regions
		for (std::size_t i = 0; i < r.size(); i++) {
			// add closed point interval for each root
			regions.insert( new CADInterval(r.at(i), c) );

			// add (-inf, x) for first root x
			if (i == 0)
				regions.insert( new CADInterval(RAN(0), r.at(i), CADInterval::CADBoundType::INF, CADInterval::CADBoundType::OPEN, c) );
			
			// for last root x add (x, inf)
			if (i == r.size()-1) {
				regions.insert( new CADInterval(r.at(i), RAN(0), CADInterval::CADBoundType::OPEN, CADInterval::CADBoundType::INF, c) );
			} else { // add open interval to next root
				regions.insert( new CADInterval(r.at(i), r.at(i+1), c) );
			}
		}

		return regions;
	}


	/** @brief gets unsat intervals for depth i corresponding to given sample map
	 * 
	 * @returns unsat intervals ordered by lower bound, ascending
	 * 
	 * (Paper Alg. 1)
	*/
	template<typename CADIntervalBased>
	std::set<CADInterval*, SortByLowerBound> get_unsat_intervals(
		CADIntervalBased& cad,			/**< corresponding CAD */ 
		const Assignment& samples,				/**< values for variables of depth till i-1 (only used if dimension is > 1) */
		carl::Variable currVar			/**< variable of current depth i */
	) {

		/* constraints are filtered for ones with main var currVar or higher */
		std::vector<ConstraintT> constraints;
		for(auto c : cad.getConstraints()) {
			auto consvars = c.variables();
			bool found_cur_var = false;
			bool found_higher_var = false;
			for(auto v : consvars.underlyingVariables()) {
				if (cad.getDepthOfVar(v) == cad.getDepthOfVar(currVar)) {
					found_cur_var = true;
				}
				if (cad.getDepthOfVar(v) > cad.getDepthOfVar(currVar)) {
					found_higher_var = true;
					break;
				}
			}
			if (found_cur_var && !found_higher_var) {
				constraints.push_back(c);
			}
		}

		// build model
		carl::Model<Rational, Poly> model;
		for(auto sample : samples)
			model.assign(sample.first, sample.second);

		/* gather intervals from each constraint */
		std::set<CADInterval*, SortByLowerBound> newintervals;
		for(auto c : constraints) {
			auto mv = carl::model::evaluate(c, model);

			/* if unsat, return (-inf, +inf) */
			if(mv.isBool()) {
				if(!mv.asBool()) {
					newintervals.clear();
					newintervals.insert(new CADInterval(c));
					SMTRAT_LOG_INFO("smtrat.cdcad", "Found trivial conflict: " << c << " with " << samples);
					return newintervals;
				}
				/* if sat, constraint is finished */
				else if(mv.asBool()) {
					SMTRAT_LOG_INFO("smtrat.cdcad", "Constraint " << c << " sat.");
					continue;
				}
			}
			else {
				// get unsat intervals for constraint
				auto regions = calcRegionsFromPoly(cad, c, samples, currVar);
				SMTRAT_LOG_TRACE("smtrat.cdcad", "Constraint " << c << " yields " << regions);
				for(auto region : regions) {
					auto r = region->getRepresentative();
					SMTRAT_LOG_TRACE("smtrat.cdcad", "Sample " << r << " from " << region);
					carl::Model modeladd = carl::Model(model);
					modeladd.assign(currVar, r);
					auto mvadd = carl::model::evaluate(c, modeladd);
					if(mvadd.isBool() && !mvadd.asBool()) {
						if(region->getLowerBoundType() != CADInterval::CADBoundType::INF) {
							region->addLowerReason(c.lhs());
						}
						if(region->getUpperBoundType() != CADInterval::CADBoundType::INF) {
							region->addUpperReason(c.lhs());
						}
						region->addReasons({c});
						newintervals.insert(region);
						SMTRAT_LOG_INFO("smtrat.cdcad", c << " is unsat, excluding " << region);
					}
					else {
						SMTRAT_LOG_TRACE("smtrat.cdcad", c << " is sat");
					}
				} 
			}
		}
		SMTRAT_LOG_TRACE("smtrat.cdcad", "Result: " << newintervals);
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
	std::tuple<bool, RAN, CADInterval::CADBoundType, std::set<CADInterval*, SortByLowerBound>> getLowestUpperBound(
		CADIntervalBased& cad,								/**< corresponding CAD */
		const std::set<CADInterval*, SortByLowerBound>& intervals	/**< set of intervals to be checked for unexplored regions */
	) {
		// check whether there are intervals
		if(intervals.empty()) {
			auto tuple = std::make_tuple(false, (RAN) 0, CADInterval::CADBoundType::OPEN, std::set<CADInterval*, SortByLowerBound>());
			// SMTRAT_LOG_INFO("smtrat.cdcad", "Invervals empty");
			return tuple;
		}

		// check for (-inf, +inf) interval
		for(auto inter : intervals) {
			if(inter->isInfinite()) {
				auto infset = std::set<CADInterval*, SortByLowerBound>();
				infset.insert(inter);
				auto tuple = std::make_tuple(false, (RAN) 0, CADInterval::CADBoundType::OPEN, infset);
				// SMTRAT_LOG_INFO("smtrat.cdcad", "Found (-oo, +oo): " << inter);
				return tuple;
			}
		}

		// get the largest interval with -inf bound
		CADInterval* start = *(intervals.begin());
		for(auto inter : intervals) {
			if(inter->getLowerBoundType() == CADInterval::CADBoundType::INF) {
				if(start->getUpper() < inter->getUpper())				
					start = inter;
				else if(start->getUpper() == inter->getUpper() && start->getUpperBoundType() == CADInterval::CADBoundType::OPEN && inter->getUpperBoundType() == CADInterval::CADBoundType::CLOSED)
					start = inter;
			}
			// as intervals are ordered, there are no further intervals starting with -inf
			else break;
		}
		// if -inf is no bound in any interval, there is some unexplored region before the first interval
		if(start->getLowerBoundType() != CADInterval::CADBoundType::INF) {
			auto tuple = std::make_tuple(true, (RAN) 0, CADInterval::CADBoundType::INF, std::set<CADInterval*, SortByLowerBound>());
			// SMTRAT_LOG_INFO("smtrat.cdcad", "Computing covering failed, no (-oo, a) interval");
			return tuple;
		}
		else {
			// SMTRAT_LOG_INFO("smtrat.cdcad", "Computing covering, found largest starting interval: " << start);
		}

		std::set<CADInterval*, SortByLowerBound> cover;

		// add (-inf, u)
		cover.insert(start);
		// SMTRAT_LOG_INFO("smtrat.cdcad", "Computing covering started, added: " << start);
		RAN highestbound = start->getUpper();
		CADInterval::CADBoundType boundopen = start->getUpperBoundType();

		// iteratively check for highest reachable bound
		// max number of added intervals is #intervals and start is already included -> 1 update
		size_t nupdated = 1;
		while(nupdated < intervals.size()) {
			bool updated = false;
			for(auto inter : intervals) {
				updated = false;
				
				// ignore start intervals, the current start was added before
				if(inter->getLowerBoundType() == CADInterval::CADBoundType::INF)
					continue;

				// if upperbound is == highestbound but was formerly not included, update
				// u) -> u]
				else if(highestbound == inter->getUpper() && boundopen == CADInterval::CADBoundType::OPEN && inter->getUpperBoundType() == CADInterval::CADBoundType::CLOSED) {
					cover.insert(inter);
					// SMTRAT_LOG_INFO("smtrat.cdcad", "Computing covering, added: " << inter << " , highest bound: " << highestbound);
					boundopen = CADInterval::CADBoundType::CLOSED;
					updated = true;
				}

				// if lowerbound == highestbound
				// (l == (l
				else if(highestbound == inter->getLower()) { // (-inf,b) is excluded above
					// rule out case where lowerbound value is excluded
					// ignore case (l, u) (u, b) as [u] is excluded
					if(boundopen == CADInterval::CADBoundType::OPEN && inter->getLowerBoundType() == CADInterval::CADBoundType::OPEN)
						continue;
					// update highestbound
					// (l, u) + [u, b]/) or (l, u] + (u, b]/) or (l, u] + [u, b]/)
					else if(inter->getUpperBoundType() != CADInterval::CADBoundType::INF) {
						cover.insert(inter);
						// SMTRAT_LOG_INFO("smtrat.cdcad", "Computing covering, added: " << inter << " , highest bound: " << highestbound);
						highestbound = inter->getUpper();
						boundopen = inter->getUpperBoundType();
						updated = true;
					}
					// if upperbound is +inf, cover was completed and there is no highest bound
					// (l, u]/) + [/(u, +inf) with [u] included
					else if(inter->getUpperBoundType() == CADInterval::CADBoundType::INF) {
						cover.insert(inter);
						// SMTRAT_LOG_INFO("smtrat.cdcad", "Computing covering, added: " << inter << " , highest bound: " << highestbound );
						auto tuple = std::make_tuple(false, (RAN) 0, CADInterval::CADBoundType::OPEN, cover);
						// SMTRAT_LOG_INFO("smtrat.cdcad", "Found cover: " << cover);
						return tuple;
					}
				}

				// if highestbound is included in inter
				// h \in (l, u)
				else if(inter->contains(highestbound)) {
					// if the interval is infinite, cover was found
					if(inter->getUpperBoundType() == CADInterval::CADBoundType::INF) {
						cover.insert(inter);
						// SMTRAT_LOG_INFO("smtrat.cdcad", "Computing covering, added: " << inter);
						auto tuple = std::make_tuple(false, (RAN) 0, CADInterval::CADBoundType::OPEN, cover);
						// SMTRAT_LOG_INFO("smtrat.cdcad", "Found cover: " << cover);
						return tuple;
					}
					// else update upper bound
					else {
						cover.insert(inter);
						// SMTRAT_LOG_INFO("smtrat.cdcad", "Computing covering, added: " << inter << " , highest bound: " << highestbound);
						highestbound = inter->getUpper();
						boundopen = inter->getUpperBoundType();
						updated = true;
					}
				} 
			}
			// if the highest bound could not be updated (& was not +inf), stop here.
			// (necessary to get to termination if not all intervals were added)
			if(!updated)
				break;
			else
				nupdated++;
		}
		
		auto tuple = std::make_tuple(true, highestbound, boundopen, std::set<CADInterval*, SortByLowerBound>());
		// SMTRAT_LOG_INFO("smtrat.cdcad", "Computing covering finished, no cover with highest bound: " << highestbound);
		return tuple;
	}


	/**@brief computes a cover from the given set of intervals
	 * 
	 * @returns subset of intervals that form a cover or an empty set if none was found
	 * (Paper Alg. 2)
	 */
	template<typename CADIntervalBased>
	std::set<CADInterval*, SortByLowerBound> compute_cover(
		CADIntervalBased& cad, 							/**< corresponding CAD */
		const std::set<CADInterval*, SortByLowerBound>& inters	/**< set of intervals over which to find a cover */
	) {
		// return cover or empty set if none was found
		auto boundtuple = getLowestUpperBound(cad, inters);
		// SMTRAT_LOG_INFO("smtrat.cdcad", "Result: " << std::get<3>(boundtuple));
		return std::get<3>(boundtuple);
	}

	/** @brief computes the next sample
	 * 
	 * Chooses a Sample outside the currently known unsat intervals
	 * 
	 * @returns RAN in unexplored interval
	 * @note check whether an unsat cover has been found before calling this!
	 */
	// todo logging
	template<typename CADIntervalBased>
	RAN chooseSample(
		CADIntervalBased& cad,							/**< corresponding CAD */
		const std::set<CADInterval*, SortByLowerBound>& inters	/**< known unsat intervals */
	) {
		bool hasminf = false;
		bool first = false;
		RAN current = RAN(0);
		auto curbound = CADInterval::CADBoundType::OPEN;
		RAN lowest = RAN(0);
		for (const auto& inter: inters) {
			if (inter->getLowerBoundType() == CADInterval::CADBoundType::INF) {
				assert(inter->getUpperBoundType() == CADInterval::CADBoundType::OPEN);
				if (!hasminf || current < inter->getUpper()) {
					current = inter->getUpper();
				}
				hasminf = true;
			} else {
				if (first) {
					lowest = inter->getLower();
					first = true;
				} else if (inter->getLower() < lowest) {
					lowest = inter->getLower();
				}
			}
		}

		if (!hasminf) {
			SMTRAT_LOG_INFO("smtrat.cdcad", "Sample below " << lowest);
			return sampleBelow(lowest);
		}

		SMTRAT_LOG_INFO("smtrat.cdcad", "Start with " << current);
		for (const auto& inter: inters) {
			if (inter->getLowerBoundType() == CADInterval::CADBoundType::INF) continue;
			if (inter->getLower() < current) {
				assert(inter->getUpperBoundType() != CADInterval::CADBoundType::INF);
				if (current < inter->getUpper()) {
					SMTRAT_LOG_INFO("smtrat.cdcad", "Overlapping with " << inter);
					assert(inter->getUpperBoundType() != CADInterval::CADBoundType::CLOSED);
					current = inter->getUpper();
					curbound = inter->getUpperBoundType();
				}
			} else if (inter->getLower() == current) {
				if (inter->getLowerBoundType() == CADInterval::CADBoundType::CLOSED) {
					SMTRAT_LOG_INFO("smtrat.cdcad", "Connecting with " << inter);
					assert(inter->getLower() == inter->getUpper());
					curbound = inter->getUpperBoundType();
				} else if (curbound == CADInterval::CADBoundType::CLOSED) {
					SMTRAT_LOG_INFO("smtrat.cdcad", "Connecting with " << inter);
					current = inter->getUpper();
					curbound = inter->getUpperBoundType();
				} else {
					SMTRAT_LOG_INFO("smtrat.cdcad", "Found sample " << current);
					return current;
				}
			} else {
				SMTRAT_LOG_INFO("smtrat.cdcad", "Found sample between " << current << " and " << inter->getLower());
				return sampleBetween(current, inter->getLower());
			}
			assert(curbound != CADInterval::CADBoundType::INF);
		}
		SMTRAT_LOG_INFO("smtrat.cdcad", "Sample above " << current);
		return sampleAbove(current);
/*
		// if -inf is not a bound find sample in (-inf, first bound)
		bool hasminf = false;
		bool first = true;
		RAN lowestval = RAN(0);
		for(const auto& inter : inters) {
			if(inter->getLowerBoundType() == CADInterval::CADBoundType::INF) {
				hasminf = true;
				// SMTRAT_LOG_INFO("smtrat.cdcad", "Choose sample found -inf interval");
				break;
			}
			else {
				// get lowest bound
				if(first) {
					lowestval = inter->getLower();
					first = false;
				}
				else if(inter->getLower() < lowestval)
					lowestval = inter->getLower();
			}
		}
		// if no -inf bound, get val below
		if(!hasminf) {
			auto samp = sampleBelow(lowestval);
			// SMTRAT_LOG_INFO("smtrat.cdcad", "Choose sample (no -inf interval): " << samp);
			return samp;
		}

		// get lowest upper bound of explored unsat regions (followed by unexplored region)
		auto boundtuple = getLowestUpperBound(cad, inters);
		//@todo handle the following instead of assertion? should not happen
		assert(std::get<0>(boundtuple) && std::get<2>(boundtuple) != CADInterval::CADBoundType::INF);
		RAN bound = std::get<1>(boundtuple);
		CADInterval::CADBoundType type = std::get<2>(boundtuple);
		// SMTRAT_LOG_INFO("smtrat.cdcad", "Choose sample: last bound at " << bound);
		SMTRAT_LOG_INFO("smtrat.cdcad", "Lowest upper bound: " << bound);

		// get unexplored region
		// lower bound of next region is right after the lowest upper bound
		// a) -> [a and a] -> (a
		if(type == CADInterval::CADBoundType::OPEN)
			type = CADInterval::CADBoundType::CLOSED;
		else if(type == CADInterval::CADBoundType::CLOSED) {
			// SMTRAT_LOG_INFO("smtrat.cdcad", "Choose sample: last bound closed");
			type = CADInterval::CADBoundType::OPEN;
		}
		// note: at this point the bound is not -inf (case is handled above)
		// SMTRAT_LOG_INFO("smtrat.cdcad", "Choose sample: lower bound at " << bound);

		// get lower bound of next interval after the unexplored region iff one exists
		bool found = false;
		// init next interval with lower bound and highest upper bound
		CADInterval* upperbound = new CADInterval;
		for(const auto& inter : inters) {
			// first take any interval with greater lower bound
			if(!found && bound < inter->getLower() && inter->getLowerBoundType() != CADInterval::CADBoundType::INF) {
				upperbound = inter;
				found = true;
				SMTRAT_LOG_INFO("smtrat.cdcad", "Moving upper bound: " << upperbound);
			}
			// if this is not the first interval to be found, update if lower
			else if(found && bound < inter->getLower() && inter->getLowerBoundType() != CADInterval::CADBoundType::INF) {
				if(inter->isLowerThan(*upperbound)) {
					upperbound = inter;
					// SMTRAT_LOG_INFO("smtrat.cdcad", "Choose sample: new upper bound " << upperbound);
					SMTRAT_LOG_INFO("smtrat.cdcad", "Moving upper bound: " << upperbound);
				}
			}
			// todo another case if inter->getLower() == bound, different types?
		}
		
		// if none was found, next bound is +inf
		CADInterval* sampleinterval;
		if(!found) {
			sampleinterval = new CADInterval(bound, RAN(0), type, CADInterval::CADBoundType::INF, ConstraintT());
			// SMTRAT_LOG_INFO("smtrat.cdcad", "Choose sample: upper bound is oo");
			
		}
		else {
			// SMTRAT_LOG_INFO("smtrat.cdcad", "Choose sample: upper bound at " << upperbound);
			// create interval in which to find the next sample (turn upper bound type to get right bound)
			auto uppertype = (upperbound->getUpperBoundType() == CADInterval::CADBoundType::OPEN) ? CADInterval::CADBoundType::CLOSED : CADInterval::CADBoundType::OPEN;
			sampleinterval = new CADInterval(bound, upperbound->getLower(), type, uppertype, ConstraintT());
		}

		SMTRAT_LOG_INFO("smtrat.cdcad", "Choose sample from " << sampleinterval);
		auto samp = sampleinterval->getRepresentative();
		SMTRAT_LOG_INFO("smtrat.cdcad", "Choosen sample " << samp << " from intervals " << inters);
		return samp;
*/
	}


	/** 
	 * @brief get all coefficients required for the given sample set
	 * 
	 * @returns set with coefficients and responsible constraint
	 * (Paper Alg. 5)
	*/
	template<typename CADIntervalBased>
	std::set<Poly> required_coefficients(
		CADIntervalBased& cad,					/**< corresponding CAD */
		const Assignment& samples,						/**< values for variables till depth i */
		const std::set<Poly>& polynomials,		/**< polynomials */
		carl::Variable currVar
	) {
		std::set<Poly> coeffs;
		for(const auto& mpoly : polynomials) {
			auto poly = carl::to_univariate_polynomial(mpoly, currVar);
			SMTRAT_LOG_TRACE("smtrat.cdcad", "Considering " << poly << " (in " << currVar << ")");
			while(!carl::isZero(poly)) {
				// add leading coefficient
				smtrat::Poly lcpoly = smtrat::Poly(cad::projection::normalize(carl::to_univariate_polynomial(poly.lcoeff(), currVar)));
				SMTRAT_LOG_TRACE("smtrat.cdcad", "Current coeff: " << lcpoly);
				if (!carl::is_zero(lcpoly) && !cad::projection::doesNotVanish(lcpoly)) {
					coeffs.insert(lcpoly);
				}

				if (cad::projection::doesNotVanish(lcpoly)) break;

				poly.truncate();
				continue;

				// bring samples in right form for evaluation
				carl::Model<Rational, Poly> model;
				for(auto sample : samples)
					model.assign(sample.first, sample.second);
				auto mv = carl::model::evaluate(lcpoly, model);

				// todo does this condition work?
				// if leading coeff evaluated at sample is non zero, stop
				if(mv.isRational() && mv.asRational() == Rational(0)) {
					// remove leading term
					poly.truncate();
				}
				// else break inner loop
				else break;
			}
		}

		SMTRAT_LOG_TRACE("smtrat.cdcad", "Required coefficients: " << coeffs);
		return coeffs;
	}


	/**@brief checks whether (polynom with given offset == 0) is satisfied by given sample */
	// todo make term RAN compatible
	template<typename CADIntervalBased>
	bool isSatWithOffset(
		CADIntervalBased& cad,					/**< corresponding CAD */
		carl::Variable currVar,
		const RAN& offset,								/**< offset */
	 	const Assignment& samples,						/**< values for variables till depth i-1 */
		const smtrat::Poly& poly,						/**< polynom */
		carl::Relation relation					/**< relation to use for constraint */
	) {
		SMTRAT_LOG_TRACE("smtrat.cdcad", "Checking " << poly << " over " << samples << relation << "0" );

		ConstraintT eqzero = ConstraintT(poly, relation);

		// check whether poly(samples x offset) == 0
		carl::Model<Rational, Poly> model;
		for(const auto& sample : samples)
			model.assign(sample.first, sample.second);
		model.assign(currVar, offset);
		auto mv = carl::model::evaluate(eqzero, model);

		if(mv.isBool() && mv.asBool()) {
			SMTRAT_LOG_TRACE("smtrat.cdcad", "SAT for poly " << poly << " + " << offset << relation << "0 on sample " << samples);
			return true;
		}

			SMTRAT_LOG_TRACE("smtrat.cdcad", "Not SAT for poly " << poly << " + " << offset << relation << "0 on sample " << samples);
		return false;
	}

	bool has_root_below(
		carl::Variable currVar,
		const RAN& reference,
	 	const Assignment& samples,
		const smtrat::Poly& poly
	) {
		carl::Model<Rational, Poly> model;
		for(const auto& sample : samples)
			model.assign(sample.first, sample.second);
		SMTRAT_LOG_TRACE("smtrat.cdcad", "Computing roots of " << poly << " over " << model);
		auto roots = carl::rootfinder::realRoots(carl::to_univariate_polynomial(poly, currVar), samples);
		for (const auto& r: roots) {
			if (r < reference) {
				SMTRAT_LOG_TRACE("smtrat.cdcad", "Found root " << r << " of " << poly << " below " << reference << " over " << samples);
				return true;
			}
		}
		return false;
	}

	bool has_root_above(
		carl::Variable currVar,
		const RAN& reference,
	 	const Assignment& samples,
		const smtrat::Poly& poly
	) {
		carl::Model<Rational, Poly> model;
		for(const auto& sample : samples)
			model.assign(sample.first, sample.second);
		SMTRAT_LOG_TRACE("smtrat.cdcad", "Computing roots of " << poly << " over " << model);
		auto roots = carl::rootfinder::realRoots(carl::to_univariate_polynomial(poly, currVar), samples);
		for (const auto& r: roots) {
			if (r > reference) {
				SMTRAT_LOG_TRACE("smtrat.cdcad", "Found root " << r << " of " << poly << " above " << reference << " over " << samples);
				return true;
			}
		}
		return false;
	}


	/**
	 *  @brief finds all polynoms responsible for unsat
	 * 
	 * @returns set of Polys with responsible constraints and whether these were input constraints
	 * 
	 * @note asserts that there is a cover in the given intervals
	 * (Paper Alg. 4)
	 * */
	template<typename CADIntervalBased>
	std::set<std::pair<Poly, std::vector<ConstraintT>>> construct_characterization(
		CADIntervalBased& cad,								/**< corresponding CAD */
		const Assignment& samples,									/**< values for variables till depth i */
		const std::set<CADInterval*, SortByLowerBound>& subinters,	/**< intervals containing a cover */
		carl::Variable currVar
	) {
		
		//std::set<CADInterval*, SortByLowerBound> subinters = compute_cover(cad, intervals);
		//assert(!subinters.empty());
		SMTRAT_LOG_INFO("smtrat.cdcad", "Computing characterization for " << samples << " on " << subinters);

		// create the characterization of the unsat region
		std::set<std::pair<Poly, std::vector<ConstraintT>>> characterization;
		for(const auto& inter : subinters) {
			SMTRAT_LOG_INFO("smtrat.cdcad", "-- Processing " << inter << " with (" << inter->getLowerReason() << ", " << inter->getUpperReason() << ", " << inter->getConstraints() << ", " << inter->getLowerConstraints() << ")");
			// add all polynoms not containing the main var
			if(inter->getLowerConstraints().empty())
				SMTRAT_LOG_TRACE("smtrat.cdcad", "---- No lower-dimensional constraints to add in " << inter);
			for(const auto& lowpoly : inter->getLowerConstraints()) {
				characterization.insert(std::make_pair(lowpoly, inter->getReasons()));
				SMTRAT_LOG_INFO("smtrat.cdcad", "---- Add lower-dimensional constraints: " << lowpoly);
			}
			// add discriminant of constraints
			if(inter->getFullDim().empty())
				SMTRAT_LOG_INFO("smtrat.cdcad", "---- No constraints to compute discriminants from in " << inter);
			for(const auto& cons : inter->getFullDim()) {
				SMTRAT_LOG_TRACE("smtrat.cdcad", "---- Checking discriminant of " << cons << " from " << inter);
				smtrat::cad::UPoly upoly = carl::discriminant(carl::to_univariate_polynomial(cons, getHighestVar(cad, cons)));
				// convert polynom to multivariate
				smtrat::Poly inspoly = smtrat::Poly(cad::projection::normalize(upoly));
				if (carl::is_zero(inspoly)) continue;
				if (cad::projection::doesNotVanish(inspoly)) continue;
				characterization.insert(std::make_pair(inspoly, inter->getReasons()));
				SMTRAT_LOG_INFO("smtrat.cdcad", "---- Add discriminant " << inspoly << " from " << cons);
			}
			// add relevant coefficients
			auto coeffs = required_coefficients(cad, samples, inter->getFullDim(), currVar);
			if (!coeffs.empty()) {
				for (const auto& coeff: coeffs) {
					characterization.emplace(coeff, inter->getReasons());
				}
				SMTRAT_LOG_INFO("smtrat.cdcad", "---- Add coeffs: " << coeffs);
			}
			// add polynomials that guarantee bounds to be closest
			for(const auto& q : inter->getFullDim()) {
				SMTRAT_LOG_TRACE("smtrat.cdcad", "---- Checking resultants with " << q << " from " << inter);
				// @todo does the following correctly represent Alg. 4, l. 7-8?
				// todo ask Gereon
				// idea: P(s x \alpha) = 0, \alpha < l => P(s x l) > 0
				if (inter->getLowerBoundType() != CADInterval::CADBoundType::INF) {
					if (has_root_below(currVar, inter->getLower(), samples, q)) {
						SMTRAT_LOG_INFO("smtrat.cdcad", "---- Checking resultants of lower " << q << " from " << inter);
						for(const auto& p : inter->getLowerReason()) {
							// get polynomial from reason
							smtrat::cad::UPoly upoly = carl::resultant(
								carl::to_univariate_polynomial(p, getHighestVar(cad, p)),
								carl::to_univariate_polynomial(q, getHighestVar(cad, q))
							);
							// convert polynom to multivariate
							smtrat::Poly inspoly = smtrat::Poly(cad::projection::normalize(upoly));
							if (carl::is_zero(inspoly)) continue;
							if (cad::projection::doesNotVanish(inspoly)) continue;
							
							characterization.insert(std::make_pair(inspoly, inter->getReasons()));
							SMTRAT_LOG_INFO("smtrat.cdcad", "---- Add resultant " << inspoly);
						}
					}
				}
				// analogously: P(s x \alpha) = 0, \alpha > u => P(s x u) < 0
				if (inter->getUpperBoundType() != CADInterval::CADBoundType::INF) {
					if (has_root_above(currVar, inter->getUpper(), samples, q)) {
						SMTRAT_LOG_TRACE("smtrat.cdcad", "---- Checking resultants of upper " << q << " from " << inter);
						for(const auto& p : inter->getUpperReason()) {
							// get polynomial from reason
							smtrat::cad::UPoly upoly = carl::resultant(
								carl::to_univariate_polynomial(p, getHighestVar(cad, p)),
								carl::to_univariate_polynomial(q, getHighestVar(cad, q))
							);
							// convert polynom to multivariate
							smtrat::Poly inspoly = smtrat::Poly(cad::projection::normalize(upoly));
							if (carl::is_zero(inspoly)) continue;
							if (cad::projection::doesNotVanish(inspoly)) continue;

							characterization.insert(std::make_pair(inspoly, inter->getReasons()));
							SMTRAT_LOG_INFO("smtrat.cdcad", "---- Add resultant " << inspoly);
						}
					}
				}
				SMTRAT_LOG_TRACE("smtrat.cdcad", "---- Finished checking resultants of " << q << " from " << inter);
			}
		}

		// add resultants of upper & lower reasons
		SMTRAT_LOG_INFO("smtrat.cdcad", "-- Add resultants of upper & lower reasons");
		auto itlower = subinters.begin();
		itlower++;
		auto itupper = subinters.begin();
		while(itlower != subinters.end()) {
			for(const auto& l : (*itlower)->getLowerReason()) {
				for(const auto& u : (*itupper)->getUpperReason()) {
					
					smtrat::cad::UPoly upoly = carl::resultant(
						carl::to_univariate_polynomial(u, getHighestVar(cad, u)),
						carl::to_univariate_polynomial(l, getHighestVar(cad, l))
					);

					// convert polynomial to multivariate
					smtrat::Poly inspoly = smtrat::Poly(cad::projection::normalize(upoly));
					if (carl::is_zero(inspoly)) continue;
					if (cad::projection::doesNotVanish(inspoly)) continue;

					// add all responsible constraints
					auto orig = (*itlower)->getReasons();
					for (const auto& o: (*itupper)->getReasons()) {
						orig.emplace_back(o);
					}
					remove_duplicates(orig);

					characterization.insert(std::make_pair(inspoly, orig));
					SMTRAT_LOG_INFO("smtrat.cdcad", "---- Add resultant " << inspoly << " from " << orig);
				}
			}
			itlower++;
			itupper++;
		}

		SMTRAT_LOG_INFO("smtrat.cdcad", "Found characterization: " << characterization);
		return characterization;
	}


	/**
	 * (Paper Alg. 6)
	 * */
	template<typename CADIntervalBased>
	CADInterval* interval_from_characterization(
		CADIntervalBased& cad,					/**< corresponding CAD */
	 	const Assignment& samples,						/**< values for variables till depth i-1 */
		carl::Variable currVar,					/**< var of depth i (current depth) */
		const RAN& val, 								/**< value for currVar */
		const std::set<std::pair<Poly, std::vector<ConstraintT>>>& butler /**< poly characterization */
	) {
		SMTRAT_LOG_TRACE("smtrat.cdcad", "Current sample " << samples << ", considering " << currVar << " = " << val);
		SMTRAT_LOG_TRACE("smtrat.cdcad", "Computing interval from characterization: " << butler);
		// partition polynomials for containing currVar
		std::set<Poly> lowdim;
		std::set<Poly> fulldim;
		std::vector<ConstraintT> constraints;

		std::set<RAN> realroots;
		for (const auto& tuple : butler) {
			auto poly = tuple.first;
			if(!poly.has(currVar))
				insert_factorized(lowdim, poly);
			else {
				insert_factorized(fulldim, poly);
				// store the real roots with substituted values until depth i-1
				auto roots = carl::rootfinder::realRoots(carl::to_univariate_polynomial(poly, currVar), samples);
				realroots.insert(roots.begin(), roots.end());
			}
			constraints.insert(constraints.end(), tuple.second.begin(), tuple.second.end());
		}
		remove_duplicates(constraints);
		
		SMTRAT_LOG_TRACE("smtrat.cdcad", "Found roots " << realroots);

		// find lower/upper bounds in roots
		bool foundlower = false;
		bool foundupper = false;
		RAN lower;
		RAN upper;
		for(const auto& r : realroots) {
			// is the root a max lower bound
			if(!foundlower && r <= val) {
				foundlower = true;
				lower = r;
			}
			else if(foundlower && r <= val && r > lower)
				lower = r;

			// is the root a min upper bound
			if(!foundupper && r >= val) {
				foundupper = true;
				upper = r;
			}
			else if(foundupper && r >= val && r < upper)
				upper = r;
		}

		if (foundlower) {
			SMTRAT_LOG_TRACE("smtrat.cdcad", "Found lower bound " << lower);
		}
		if (foundupper) {
			SMTRAT_LOG_TRACE("smtrat.cdcad", "Found upper bound " << upper);
		}

		// find reasons for bounds
		std::set<Poly> lowerres;
		std::set<Poly> upperres; 
		for(const auto& poly : fulldim) {
			//@todo is the isSatWithOffset function what was meant in Alg. 6, l. 6-7?
			// todo ask Gereon
			// if no lower bound was found it is -inf, no conss will bound it
			if(foundlower) {
				if(isSatWithOffset(cad, currVar, lower, samples, poly, carl::Relation::EQ)) {
					insert_factorized(lowerres, poly);
				}
			}
			// analogously to lower bound
			if(foundupper) {
				if(isSatWithOffset(cad, currVar, upper, samples, poly, carl::Relation::EQ)) {
					insert_factorized(upperres, poly);
				}
			}
		}
		SMTRAT_LOG_TRACE("smtrat.cdcad", "Reasons: " << lowerres << " and " << upperres << " from " << fulldim);

		// determine bound types
		// todo is that correct?
		CADInterval::CADBoundType lowertype = CADInterval::CADBoundType::OPEN;
		CADInterval::CADBoundType uppertype = CADInterval::CADBoundType::OPEN;
		if(!foundlower){
			lowertype = CADInterval::CADBoundType::INF;
			lower = (RAN) 0;
		} else if (val == lower) {
			lowertype = CADInterval::CADBoundType::CLOSED;
		}
		if(!foundupper){
			uppertype = CADInterval::CADBoundType::INF;
			upper = (RAN) 0;
		} else if (val == upper) {
			uppertype = CADInterval::CADBoundType::CLOSED;
		}

		return new CADInterval(lower, upper, lowertype, uppertype, lowerres, upperres, fulldim, lowdim, {});
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
	std::tuple<bool, std::set<CADInterval*, SortByLowerBound>, Assignment> get_unsat_cover(
		CADIntervalBased& cad,					/**< corresponding CAD */
		const Assignment& samples,						/**< values for variables of depth i-1 (initially empty set) */
		carl::Variable currVar					/**< var of depth i (current depth) */
	) {
		SMTRAT_LOG_INFO("smtrat.cdcad", "***** with " << samples << " for " << currVar);
		// get known unsat intervals
		auto unsatinters = get_unsat_intervals(cad, samples, currVar);
		SMTRAT_LOG_INFO("smtrat.cdcad", "I := " << unsatinters);

		// run until a cover was found
		while(compute_cover(cad, unsatinters).empty()) {
			// add new sample for current variable
			auto newsamples = new Assignment(samples);
			RAN newval = chooseSample(cad, unsatinters);
			SMTRAT_LOG_INFO("smtrat.cdcad", "Sampled " << currVar << " := " << newval);
			newsamples->insert(std::make_pair(currVar, newval));

			// if the sample set has full dimension we have a satifying witness
			if(cad.dim() == cad.getDepthOfVar(currVar))
				return std::make_tuple(true, std::set<CADInterval*, SortByLowerBound>(), *newsamples);

			// recursive recall for next dimension
			auto nextcall = get_unsat_cover(cad, *newsamples, cad.getNextVar(currVar));
			// if SAT
			if(std::get<0>(nextcall))
				return nextcall;
			else {
				SMTRAT_LOG_TRACE("smtrat.cdcad", "Computing new unsat interval for " << currVar);
				// get subset of intervals that has no intervals contained in any other one
				auto covering = compute_cover(cad, std::get<1>(nextcall));
				assert(!covering.empty());
				auto butler = construct_characterization(cad, *newsamples, covering, cad.getNextVar(currVar));
				CADInterval* butlerinter = interval_from_characterization(cad, samples, currVar, newval, butler);
				for (const auto& c: covering) {
					butlerinter->addReasons(c->getReasons());
				}
				SMTRAT_LOG_INFO("smtrat.cdcad", "Adding " << butlerinter << " with (" << butlerinter->getLowerReason() << ", " << butlerinter->getUpperReason() << ", " << butlerinter->getConstraints() << ", " << butlerinter->getLowerConstraints() << ")");
				unsatinters.insert(butlerinter);
				SMTRAT_LOG_INFO("smtrat.cdcad", "I := " << unsatinters);
			}
		}

		// in case the loop exits a cover was found
		SMTRAT_LOG_INFO("smtrat.cdcad", "Unsat cover found for " << currVar);
		auto res = std::make_tuple(false, unsatinters, Assignment());
		SMTRAT_LOG_INFO("smtrat.cdcad", "***** done for " << currVar);
		return res;
	}


	template<typename CADIntervalBased>
	Answer operator()(Assignment& assignment, CADIntervalBased& cad) {
		// look for unsat cover
		auto res = get_unsat_cover(cad, Assignment(), cad.getVariables().at(0));
		Answer ans = std::get<0>(res) ? Answer::SAT : Answer::UNSAT;
		SMTRAT_LOG_INFO("smtrat.cdcad", "Found answer: " << ans);		

		// if no cover was found, set SAT assignment
		if(ans == Answer::SAT)
			assignment = std::get<2>(res);
		else {
			assignment = Assignment();
			FormulaSetT cover;
			for(const auto& inter : std::get<1>(res)) {
				SMTRAT_LOG_INFO("smtrat.cdcad", "Adding " << inter->getReasons() << " from " << inter);		
				// add constraints that where directly responsible
				for(const auto& cons : inter->getReasons())
					cover.insert(carl::Formula(cons));

				// add other constraints that where responsible
				//for(auto pair : inter->getLowerReason()) {
				//	for(auto cons : pair.second)
				//		cover.insert(carl::Formula(cons));
				//}
				//for(auto pair : inter->getUpperReason()) {
				//	for(auto cons : pair.second)
				//		cover.insert(carl::Formula(cons));
				//}
			}
			cad.setUnsatCover(cover);
		}

		return ans;
	}
};

}
}