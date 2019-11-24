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


	/** @brief gets highest var in var order that is present in the polynom
	 * 
	 * with respect to variable order in cad
	 * 
	 * @returns highest var in polynom
	*/
	template<typename CADIntervalBased>
	carl::Variable getHighestVar(
		CADIntervalBased& cad,	/**< corresponding CAD */
		smtrat::Poly poly		/**< polynom */
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
		ConstraintT c, 				/**< constraint containing the polynom */
		Assignment samples,			/**< variables to be substituted by given values, may be empty */
		carl::Variable currVar		/**< constraint is considered as univariate in this variable */
	) {
		std::set<CADInterval*, SortByLowerBound> regions;

		// find real roots of constraint corresponding to current var
		auto r = carl::rootfinder::realRoots(carl::to_univariate_polynomial(c.lhs(), currVar), samples);

		std::sort(r.begin(), r.end());

		// if there is no real root, there is just one interval: (-inf, +inf)
		if(r.empty()) {
			SMTRAT_LOG_INFO("smtrat.cdcad", "Roots of " << c << " do not exists");
			regions.insert( new CADInterval(c));
			return regions;
		}

		SMTRAT_LOG_INFO("smtrat.cdcad", "Roots of " << c << ": " << r);
		
		// go through roots to build region intervals and add them to the regions
		for (std::size_t i = 0; i < r.size(); i++) {
			// add closed point interval for each root
			regions.insert( new CADInterval(r.at(i), c) );

			// add (-inf, x) for first root x
			if (i == 0)
				regions.insert( new CADInterval(RAN(0), r.at(i), CADInterval::CADBoundType::INF, CADInterval::CADBoundType::OPEN, c) );
			
			// for last root x add (x, inf)
			if (i == r.size()-1) {
				SMTRAT_LOG_INFO("smtrat.cdcad", "Adding region up to oo");
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
		Assignment samples,				/**< values for variables of depth till i-1 (only used if dimension is > 1) */
		carl::Variable currVar			/**< variable of current depth i */
	) {

		/* constraints are filtered for ones with main var currVar or higher */
		std::vector<ConstraintT> constraints;
		for(auto c : cad.getConstraints()) {
			auto consvars = c.variables();
			for(auto v : consvars.underlyingVariables()) {
				if(isAtLeastCurrVar(cad, v, currVar)) {
					constraints.push_back(c);
					break;
				}
			}
		}
		SMTRAT_LOG_INFO("smtrat.cdcad", "Using " << constraints);

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
				SMTRAT_LOG_INFO("smtrat.cdcad", "Constraint " << c << " yields " << regions);
				for(auto region : regions) {
					auto r = region->getRepresentative();
					SMTRAT_LOG_INFO("smtrat.cdcad", "Sample " << r << " from " << region);
					carl::Model modeladd = carl::Model(model);
					modeladd.assign(currVar, r);
					auto mvadd = carl::model::evaluate(c, modeladd);
					if(mv.isBool() && !mvadd.asBool()) {
						SMTRAT_LOG_INFO("smtrat.cdcad", c << " is unsat on " << modeladd);
						std::vector<ConstraintT> origin;
						origin.push_back(c);
						if(region->getLowerBoundType() != CADInterval::CADBoundType::INF)
							region->addLowerReason(std::make_pair(c.lhs(), origin));
						if(region->getUpperBoundType() != CADInterval::CADBoundType::INF)
							region->addUpperReason(std::make_pair(c.lhs(), origin));
						region->addConstraint(c);
						newintervals.insert(region);
						SMTRAT_LOG_INFO("smtrat.cdcad", "Added " << region << " to unsat intervals.");
					}
				} 
			}
		}
		SMTRAT_LOG_INFO("smtrat.cdcad", "Result: " << newintervals);
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
		std::set<CADInterval*, SortByLowerBound> intervals	/**< set of intervals to be checked for unexplored regions */
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
	std::set<CADInterval*, SortByLowerBound>compute_cover(
		CADIntervalBased& cad, 							/**< corresponding CAD */
		std::set<CADInterval*, SortByLowerBound> inters	/**< set of intervals over which to find a cover */
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
		std::set<CADInterval*, SortByLowerBound> inters	/**< known unsat intervals */
	) {
		// if -inf is not a bound find sample in (-inf, first bound)
		bool hasminf = false;
		bool first = true;
		RAN lowestval = RAN(0);
		for(auto inter : inters) {
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
		for(auto inter : inters) {
			// first take any interval with greater lower bound
			if(!found && bound < inter->getLower() && inter->getLowerBoundType() != CADInterval::CADBoundType::INF) {
				upperbound = inter;
				found = true;
			}
			// if this is not the first interval to be found, update if lower
			else if(found && bound < inter->getLower() && inter->getLowerBoundType() != CADInterval::CADBoundType::INF) {
				if(inter->isLowerThan(*upperbound)) {
					upperbound = inter;
					// SMTRAT_LOG_INFO("smtrat.cdcad", "Choose sample: new upper bound " << upperbound);
				}
			}
			// todo another case if inter->getLower() == bound, different types?
		}
		
		// if none was found, next bound is +inf
		CADInterval* sampleinterval;
		if(!found) {
			sampleinterval = new CADInterval(bound, RAN(0), type, CADInterval::CADBoundType::INF);
			// SMTRAT_LOG_INFO("smtrat.cdcad", "Choose sample: upper bound is oo");
			
		}
		else {
			// SMTRAT_LOG_INFO("smtrat.cdcad", "Choose sample: upper bound at " << upperbound);
			// create interval in which to find the next sample (turn upper bound type to get right bound)
			auto uppertype = (upperbound->getUpperBoundType() == CADInterval::CADBoundType::OPEN) ? CADInterval::CADBoundType::CLOSED : CADInterval::CADBoundType::OPEN;
			sampleinterval = new CADInterval(bound, upperbound->getLower(), type, uppertype);
		}

		// SMTRAT_LOG_INFO("smtrat.cdcad", "Choose sample from " << sampleinterval);
		auto samp = sampleinterval->getRepresentative();
		SMTRAT_LOG_INFO("smtrat.cdcad", "Choosen sample " << samp << " from intervals " << inters);
		return samp;
	}


	/** 
	 * @brief get all coefficients required for the given sample set
	 * 
	 * @returns set with coefficients and responsible constraint
	 * (Paper Alg. 5)
	*/
	template<typename CADIntervalBased>
	std::set<std::pair<Poly, std::vector<ConstraintT>>> required_coefficients(
		CADIntervalBased& cad,					/**< corresponding CAD */
		Assignment samples,						/**< values for variables till depth i */
		std::set<ConstraintT> constraints		/**< constraints */
	) {
		std::set<std::pair<Poly, std::vector<ConstraintT>>> coeffs;
		for(auto cons : constraints) {
			auto poly = cons.lhs();
			std::vector<ConstraintT> orig;
			orig.push_back(cons);
			while(!carl::isZero(poly)) {
				// add leading coefficient
				smtrat::Poly lcpoly = smtrat::Poly(poly.lcoeff());
				coeffs.insert(std::make_pair(lcpoly, orig));

				// bring samples in right form for evaluation
				carl::Model<Rational, Poly> model;
				for(auto sample : samples)
					model.assign(sample.first, sample.second);
				auto mv = carl::model::evaluate(lcpoly, model);

				// todo does this condition work?
				// if leading coeff evaluated at sample is non zero, stop
				if(mv.isRational() && mv.asRational() == Rational(0)) {
					// remove leading term
					poly = poly.stripLT();
				}
				// else break inner loop
				else break;
			}
		}

		return coeffs;
	}


	/**@brief checks whether (polynom with given offset == 0) is satisfied by given sample */
	// todo make term RAN compatible
	template<typename CADIntervalBased>
	bool isSatWithOffset(
		CADIntervalBased& cad,					/**< corresponding CAD */
		RAN offset,								/**< offset */
	 	Assignment samples,						/**< values for variables till depth i-1 */
		smtrat::Poly poly,						/**< polynom */
		carl::Relation relation					/**< relation to use for constraint */
	) {
		smtrat::Poly offsetpoly = poly;
		// todo is Rational ok? I want a RAN! find term with rans?
		const carl::Term<smtrat::Rational>* term = new carl::Term(offset.value());
		offsetpoly.addTerm((*term)); // @todo is this what is meant in alg.6, l.6-7?
		ConstraintT eqzero = ConstraintT(offsetpoly, relation);

		// check whether poly(samples x offset) == 0
		carl::Model<Rational, Poly> model;
		for(auto sample : samples)
			model.assign(sample.first, sample.second);
		auto mv = carl::model::evaluate(eqzero, model);

		if(mv.isBool() && mv.asBool())
			return true;

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
		Assignment samples,									/**< values for variables till depth i */
		std::set<CADInterval*, SortByLowerBound> intervals	/**< intervals containing a cover */
	) {
		// todo
		// get subset of intervals that has no intervals contained in any other one
		std::set<CADInterval*, SortByLowerBound> subinters = compute_cover(cad, intervals);
		assert(!subinters.empty());

		// create the characterization of the unsat region
		std::set<std::pair<Poly, std::vector<ConstraintT>>> characterization;
		for(auto inter : subinters) {
			// add all polynoms not containing the main var
			for(auto lowpoly : inter->getLowerConstraints()) {
				std::vector<ConstraintT> orig;
				orig.push_back(lowpoly);
				characterization.insert(std::make_pair(lowpoly.lhs(), orig));
			}
			// add discriminant of constraints
			for(auto cons : inter->getConstraints()) {
				smtrat::cad::UPoly upoly = carl::discriminant(carl::to_univariate_polynomial(cons.lhs(), getHighestVar(cad, cons.lhs())));
				// convert polynom to multivariate
				smtrat::Poly inspoly = smtrat::Poly(upoly);
				std::vector<ConstraintT> orig;
				orig.push_back(cons);
				characterization.insert(std::make_pair(inspoly, orig));
			}
			// add relevant coefficients
			auto coeffs = required_coefficients(cad, samples, inter->getConstraints());
			characterization.insert(coeffs.begin(), coeffs.end());
			// add polynomials that guarantee bounds to be closest
			for(auto q : inter->getConstraints()) {
				// @todo does the following correctly represent Alg. 4, l. 7-8?
				// todo ask Gereon
				// idea: P(s x \alpha) = 0, \alpha < l => P(s x l) > 0
				if(isSatWithOffset(cad, inter->getLower(), samples, q.lhs(), carl::Relation::GREATER)) {
					for(auto ptuple : inter->getLowerReason()) {
						// get polynomial from reason
						auto p = ptuple.first;
						smtrat::cad::UPoly upoly = carl::resultant(
							carl::to_univariate_polynomial(p, getHighestVar(cad, p)),
							carl::to_univariate_polynomial(q.lhs(), getHighestVar(cad, q.lhs()))
						);
						// convert polynom to multivariate
						smtrat::Poly inspoly = smtrat::Poly(upoly);
						// add all responsible constraints
						std::vector<ConstraintT> orig;
						orig.push_back(q);
						for(auto cons : ptuple.second) {
							orig.push_back(cons);
						}
						
						characterization.insert(std::make_pair(inspoly, orig));
					}
				}
				// analogously: P(s x \alpha) = 0, \alpha > u => P(s x u) < 0
				if(isSatWithOffset(cad, inter->getUpper(), samples, q.lhs(), carl::Relation::LESS)) {
					for(auto ptuple : inter->getUpperReason()) {
						// get polynomial from reason
						auto p = ptuple.first;
						smtrat::cad::UPoly upoly = carl::resultant(
							carl::to_univariate_polynomial(p, getHighestVar(cad, p)),
							carl::to_univariate_polynomial(q.lhs(), getHighestVar(cad, q.lhs()))
						);
						// convert polynom to multivariate
						smtrat::Poly inspoly = smtrat::Poly(upoly);

						// add all responsible constraints
						std::vector<ConstraintT> orig;
						orig.push_back(q);
						for(auto cons : ptuple.second) {
							orig.push_back(cons);
						}

						characterization.insert(std::make_pair(inspoly, orig));
					}
				}
			}
		}

		// add resultants of upper & lower reasons
		auto itlower = subinters.begin();
		itlower++;
		auto itupper = subinters.begin();
		while(itlower != subinters.end()) {
			for(auto lower : (*itlower)->getLowerReason()) {
				auto l = lower.first;
				for(auto upper : (*itupper)->getUpperReason()) {
					auto u = upper.first;
					
					smtrat::cad::UPoly upoly = carl::resultant(
						carl::to_univariate_polynomial(u, getHighestVar(cad, u)),
						carl::to_univariate_polynomial(l, getHighestVar(cad, l))
					);

					// convert polynomial to multivariate
					smtrat::Poly inspoly = smtrat::Poly(upoly);

					// add all responsible constraints
					std::vector<ConstraintT> orig;
					for(auto cons : lower.second) {
						orig.push_back(cons);
					}
					for(auto cons : upper.second) {
						orig.push_back(cons);
					}

					characterization.insert(std::make_pair(inspoly, orig));
				}
			}
			itlower++;
			itupper++;
		}

		return characterization;
	}


	/**
	 * (Paper Alg. 6)
	 * */
	template<typename CADIntervalBased>
	CADInterval* interval_from_characterization(
		CADIntervalBased& cad,					/**< corresponding CAD */
	 	Assignment samples,						/**< values for variables till depth i-1 */
		carl::Variable currVar,					/**< var of depth i (current depth) */
		RAN val, 								/**< value for currVar */
		std::set<std::pair<Poly, std::vector<ConstraintT>>> butler /**< poly characterization */
	) {
		//todo
		// partition polynomials for containing currVar
		std::set<std::pair<Poly, std::vector<ConstraintT>>> notp_i;
		std::set<std::pair<Poly, std::vector<ConstraintT>>> p_i;
		std::set<RAN> realroots;
		for(auto tuple : butler) {
			auto poly = tuple.first;
			if(!poly.has(currVar))
				notp_i.insert(tuple);
			else {
				p_i.insert(tuple);
				// store the real roots with substituted values until depth i-1
				auto roots = carl::rootfinder::realRoots(carl::to_univariate_polynomial(poly, currVar), samples);
				realroots.insert(roots.begin(), roots.end());
			}
		}

		// find lower/upper bounds in roots
		bool foundlower = false;
		bool foundupper = false;
		RAN lower;
		RAN upper;
		for(auto r : realroots) {
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

		// find reasons for bounds
		std::set<std::pair<Poly, std::vector<ConstraintT>>> lowerres;
		std::set<std::pair<Poly, std::vector<ConstraintT>>> upperres; 
		for(auto tuple : p_i) {
			//@todo is the isSatWithOffset function what was meant in Alg. 6, l. 6-7?
			// todo ask Gereon
			// if no lower bound was found it is -inf, no conss will bound it
			if(foundlower) {
				if(isSatWithOffset(cad, lower, samples, tuple.first, carl::Relation::EQ))
					lowerres.insert(tuple);
			}
			// analogously to lower bound
			if(foundupper) {
				if(isSatWithOffset(cad, upper, samples, tuple.first, carl::Relation::EQ))
					upperres.insert(tuple);
			}
		}

		// determine bound types
		// todo is that correct?
		CADInterval::CADBoundType lowertype = CADInterval::CADBoundType::OPEN;
		CADInterval::CADBoundType uppertype = CADInterval::CADBoundType::OPEN;
		if(!foundlower){
			lowertype = CADInterval::CADBoundType::INF;
			lower = (RAN) 0;
		}
		if(!foundupper){
			uppertype = CADInterval::CADBoundType::INF;
			upper = (RAN) 0;
		}
		
		// determine actual constraints
		std::set<ConstraintT> picons;
		for(auto tuple : p_i) {
			for(auto cons : tuple.second) {
				picons.insert(cons);
			}
		}
		std::set<ConstraintT> notpicons;
		for(auto tuple : notp_i) {
			for(auto cons : tuple.second) {
				notpicons.insert(cons);
			}
		}

		return new CADInterval(lower, upper, lowertype, uppertype, lowerres, upperres, picons, notpicons);
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
		Assignment samples,						/**< values for variables of depth i-1 (initially empty set) */
		carl::Variable currVar					/**< var of depth i (current depth) */
	) {
		// get known unsat intervals
		auto unsatinters = get_unsat_intervals(cad, samples, currVar);
		SMTRAT_LOG_INFO("smtrat.cdcad", "Unsat intervals: " << unsatinters);

		// run until a cover was found
		while(compute_cover(cad, unsatinters).empty()) {
			SMTRAT_LOG_INFO("smtrat.cdcad", "Choose next sample for var " << currVar);
			// add new sample for current variable
			auto newsamples = new Assignment(samples);
			RAN newval = chooseSample(cad, unsatinters);
			SMTRAT_LOG_INFO("smtrat.cdcad", "Next sample " << newval);
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
				auto butler = construct_characterization(cad, *newsamples, std::get<1>(nextcall));
				CADInterval* butlerinter = interval_from_characterization(cad, samples, currVar, newval, butler);
				unsatinters.insert(butlerinter);
			}
		}

		// in case the loop exits a cover was found
		SMTRAT_LOG_INFO("smtrat.cdcad", "Unsat cover found.");
		auto res = std::make_tuple(false, unsatinters, Assignment());
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
			for(auto inter : std::get<1>(res)) {
				for(auto cons : inter->getConstraints())
					cover.insert(carl::Formula(cons));
			}
			cad.setUnsatCover(cover);
		}

		return ans;
	}
};

}
}
