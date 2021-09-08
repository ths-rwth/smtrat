/**
 * @file Backend.h
 * @author Philip Kroll <Philip.Kroll@rwth-aachen.de>
 *
 * @version 2021-07-08
 * Created on 2021-07-08.
 */

// https://arxiv.org/pdf/2003.05633.pdf

#pragma once

#include <algorithm>

#include <carl/ran/ran.h>

#include "CoveringUtils.h"
#include "NewCoveringModule.h"
#include "NewCoveringSettings.h"

namespace smtrat {

template<typename Settings>
class Backend {
	using SettingsT = Settings;

private:
	//Variable Ordering, Initialized once in checkCore
	std::vector<carl::Variable> mVariableOrdering;

	//Main Variables of constraints need to be in the same ordering as the variable ordering
	std::vector<PolyRefVector> mConstraints;

	Helpers helpers;

	carl::ran_assignment<Rational> mCurrentAssignment;

	std::vector<std::vector<CellInformation>> mCoveringInformation;

public:
	//Init with empty variable ordering
	Backend()
		: mVariableOrdering() {
		SMTRAT_LOG_DEBUG("smtrat.covering", " Dry Init of Covering Backend");
	}

	Backend(const std::vector<carl::Variable>& varOrdering, std::vector<PolyRefVector>& constraints)
		: mVariableOrdering(varOrdering), mConstraints(constraints) {
		SMTRAT_LOG_DEBUG("smtrat.covering", "Init of Covering Backend with Variable Ordering: " << mVariableOrdering);
		mCoveringInformation.resize(mVariableOrdering.size());
	}

	size_t dimension() {
		return mVariableOrdering.size();
	}

	void setHelpers(Helpers& hp) {
		helpers = hp;
	}

	void setConstraints(std::vector<PolyRefVector>& constraints) {
		mConstraints = constraints;
	}

	void reduceConstraints() {
		for (auto& refVector : mConstraints) {
			//Remove duplicates
			refVector.reduce();
		}
	}

	std::vector<std::vector<CellInformation>>& getCoveringInformation() {
		return mCoveringInformation;
	}

	carl::ran_assignment<Rational> getCurrentAssignment() {
		return mCurrentAssignment;
	}

	//The new Variable ordering must be an "extension" to the old one
	void setVariableOrdering(const std::vector<carl::Variable>& newVarOrdering) {
		SMTRAT_LOG_DEBUG("smtrat.covering", "Old Variable ordering: " << mVariableOrdering);

		assert(newVarOrdering.size() > mVariableOrdering.size());

		for (std::size_t i = 0; i < mVariableOrdering.size(); i++) {
			assert(newVarOrdering[i] == mVariableOrdering[i]);
		}

		std::copy(newVarOrdering.begin() + mVariableOrdering.size(), newVarOrdering.end(), std::back_inserter(mVariableOrdering));
		mCoveringInformation.resize(mVariableOrdering.size());
		SMTRAT_LOG_DEBUG("smtrat.covering", "New Variable ordering: " << mVariableOrdering);
	}

	//Delete all stored data with level higher or equal
	void resetStoredData(std::size_t level) {
		for (size_t i = level; i < dimension(); i++) {
			mCoveringInformation[i].clear();
			mCurrentAssignment.erase(mVariableOrdering[i]);
		}
	}

	bool hasRootAbove(const cadcells::datastructures::PolyRef& poly, const RAN& number) {
		std::vector<RAN> roots = helpers.mProjections->real_roots(mCurrentAssignment, poly);
		SMTRAT_LOG_DEBUG("smtrat.covering", "Poly: " << helpers.mPool->get(poly) << " for assignment " << mCurrentAssignment << " : " << std::any_of(roots.begin(), roots.end(), [&number](const RAN& root) {
												return root >= number;
											}););
		return std::any_of(roots.begin(), roots.end(), [&number](const RAN& root) {
			return root >= number;
		});
	}

	bool hasRootBelow(const cadcells::datastructures::PolyRef& poly, const RAN& number) {
		std::vector<RAN> roots = helpers.mProjections->real_roots(mCurrentAssignment, poly);
		SMTRAT_LOG_DEBUG("smtrat.covering", "Poly: " << helpers.mPool->get(poly) << " for assignment " << mCurrentAssignment << " : " << std::any_of(roots.begin(), roots.end(), [&number](const RAN& root) {
												return root <= number;
											}););
		return std::any_of(roots.begin(), roots.end(), [&number](const RAN& root) {
			return root <= number;
		});
	}

	PolyRefVector requiredCoefficients(const cadcells::datastructures::PolyRef& poly) {
		PolyRefVector result;
		//Get "real" poly object to substract leading term if necessary
		carl::MultivariatePolynomial<Rational> p = helpers.mPool->get(poly);
		//SMTRAT_LOG_DEBUG("smtrat.covering", "Get required Coefficients of: " << p);
		while (!carl::is_zero(p)) {
			//SMTRAT_LOG_DEBUG("smtrat.covering", "Start While with: " << p);
			if (carl::is_constant(p)) {
				//Check is necessary because ldcf asserts that level of p > 0
				result.add(helpers.mPool->insert(p));
				break;
			}
			cadcells::datastructures::PolyRef ldcf = helpers.mProjections->ldcf(helpers.mPool->insert(p));
			//SMTRAT_LOG_DEBUG("smtrat.covering", "Found leading coefficient: " << helpers.mPool->get(ldcf));
			result.add(ldcf);
			if (helpers.mProjections->is_zero(mCurrentAssignment, ldcf)) {
				//SMTRAT_LOG_DEBUG("smtrat.covering", "Evaluated to zero at current assignment");
				break;
			}
			p = p - p.lterm();
		}

		result.reduce(); //remove duplicates
		//SMTRAT_LOG_DEBUG("smtrat.covering", "Found required Coefficients: " << result);
		return result;
	}

	PolyRefVector constructCharacterization(const std::size_t level) {
		orderAndCleanIntervals(mCoveringInformation[level + 1]);
		PolyRefVector result;
		for (const CellInformation& cell : mCoveringInformation[level + 1]) {
			result.add(cell.mBottomPolys); //Algo line 5
			for (const auto& mainPoly : cell.mMainPolys) {
				result.add(helpers.mProjections->disc(mainPoly)); //Algo line 6
				SMTRAT_LOG_DEBUG("smtrat.covering", "After adding discriminants: " << result);
				result.add(requiredCoefficients(mainPoly)); //Algo line 7
				SMTRAT_LOG_DEBUG("smtrat.covering", "After adding required coefficients: " << result);
				//Todo check if bounds are +- infty
				for (const auto& lowerReasonPoly : cell.mLowerPolys) {
					if (hasRootBelow(lowerReasonPoly, cell.mLowerBound.number.value())) {
						SMTRAT_LOG_DEBUG("smtrat.covering", "Calculating Lower Resultants: " << helpers.mPool->get(mainPoly) << "  ,  " << helpers.mPool->get(lowerReasonPoly));
						result.add(helpers.mProjections->res(mainPoly, lowerReasonPoly)); //Algo line 8
					}
				}
				for (const auto& upperReasonPoly : cell.mUpperPolys) {
					if (hasRootAbove(upperReasonPoly, cell.mUpperBound.number.value())) {
						SMTRAT_LOG_DEBUG("smtrat.covering", "Calculating Upper Resultants: " << helpers.mPool->get(mainPoly) << "  ,  " << helpers.mPool->get(upperReasonPoly));
						result.add(helpers.mProjections->res(mainPoly, upperReasonPoly)); //Algo line 9
					}
				}
			}
		}
		for (std::size_t i = 0; i < mCoveringInformation[level + 1].size() - 1; i++) {
			for (const auto& p : mCoveringInformation[level + 1][i].mUpperPolys) {
				for (const auto& q : mCoveringInformation[level + 1][i + 1].mLowerPolys) {
					SMTRAT_LOG_DEBUG("smtrat.covering", "Calculating Pair Resultants: " << helpers.mPool->get(p) << "  ,  " << helpers.mPool->get(q));
					result.add(helpers.mProjections->res(p, q)); //Algo line 11
				}
			}
		}
		//Todo: standard CAD simplifications to result vector
		result.reduce();
		return result;
	}

	CellInformation intervalFromCharacterization(const PolyRefVector& characterization, const RAN& sample, const std::size_t level) {
		PolyRefVector lowerReasons;
		PolyRefVector upperReasons;
		PolyRefVector main;
		PolyRefVector bottom;
		std::optional<RAN> l;
		std::optional<RAN> u;
		std::vector<RAN> roots;

		SMTRAT_LOG_DEBUG("smtrat.covering", "Characterization: " << characterization << " Sample: " << sample);

		for (const auto& poly : characterization) {
			if (poly.level == level) {
				main.add(poly); //Algo line 2
			} else {
				bottom.add(poly); //Algo line 1
			}
			if (helpers.mProjections->is_const(poly)) continue; // Skip if poly is constant
			std::vector<RAN> cur_roots = helpers.mProjections->real_roots(mCurrentAssignment, poly);
			roots.insert(roots.end(), cur_roots.begin(), cur_roots.end());
		}

		std::sort(roots.begin(), roots.end());
		SMTRAT_LOG_DEBUG("smtrat.covering", "Found roots: " << roots);

		auto tmp_l = std::lower_bound(roots.begin(), roots.end(), sample); //Algo line 4
		if (tmp_l != roots.end()) {
			l = *tmp_l;
		}
		SMTRAT_LOG_DEBUG("smtrat.covering", "Found Lower bound: " << l);

		auto tmp_u = std::upper_bound(roots.begin(), roots.end(), sample); //Algo line 5
		if (tmp_u != roots.end()) {
			u = *tmp_u;
		}
		SMTRAT_LOG_DEBUG("smtrat.covering", "Found Upper bound: " << u);

		if (l) { //if l is not -infty
			mCurrentAssignment[mVariableOrdering[level]] = l.value();
			for (const auto& poly : main) {
				if (helpers.mProjections->is_zero(mCurrentAssignment, poly)) {
					lowerReasons.add(poly);
				}
			}
			mCurrentAssignment.erase(mVariableOrdering[level]);
		}

		if (u) { //if u is not infty
			if (l && l.value() == u.value()) {
				//special case for u = l != +-infty
				upperReasons = lowerReasons;
				return CellInformation{LowerBound{l.value(), false}, UpperBound{l.value(), false}, main, bottom, lowerReasons, upperReasons};
			} else {
				mCurrentAssignment[mVariableOrdering[level]] = u.value();
				for (const auto& poly : main) {
					if (helpers.mProjections->is_zero(mCurrentAssignment, poly)) {

						upperReasons.add(poly);
					}
				}
				mCurrentAssignment.erase(mVariableOrdering[level]);
			}
		}

		if (!u && !l) {
			return CellInformation{LowerBound{std::nullopt, true}, UpperBound{std::nullopt, true}, main, bottom, lowerReasons, upperReasons};
		}
		if (!u) {
			return CellInformation{LowerBound{l.value(), true}, UpperBound{std::nullopt, true}, main, bottom, lowerReasons, upperReasons};
		}
		if (!l) {
			return CellInformation{LowerBound{std::nullopt, true}, UpperBound{u.value(), true}, main, bottom, lowerReasons, upperReasons};
		}
		return CellInformation{LowerBound{l.value(), true}, UpperBound{u.value(), true}, main, bottom, lowerReasons, upperReasons};
	}

	//TODO: Use substitute instead of evaluate!
	//TODO: REFACTOR!
	std::vector<CellInformation> getUnsatIntervals(const std::size_t level) {
		SMTRAT_LOG_DEBUG("smtrat.covering", "getUnsatIntervals for level: " << level);
		std::vector<CellInformation> result;
		carl::Variable mainVar = mVariableOrdering[level];
		assert(mCurrentAssignment.count(mainVar) == 0);
		for (const auto& constraint : mConstraints[level]) {
			SMTRAT_LOG_DEBUG("smtrat.covering", "Current constraint: " << helpers.mPool->get(constraint) << " ;  Current assignment: " << mCurrentAssignment);
			//Note: Roots are sorted in ascending order
			SMTRAT_LOG_DEBUG("smtrat.covering", "Mainvar: " << helpers.mProjections->main_var(constraint));
			std::vector<RAN> roots;
			if (!helpers.mProjections->is_nullified(mCurrentAssignment, constraint)) {
				roots = helpers.mProjections->real_roots(mCurrentAssignment, constraint);
			}
			SMTRAT_LOG_DEBUG("smtrat.covering", "Found roots: " << roots);
			bool wasSet = mCurrentAssignment.count(mainVar) != 0;
			RAN oldValue;
			if (wasSet) {
				oldValue = mCurrentAssignment[mainVar];
			}
			if (roots.empty()) {
				//either true or false for whole number line
				//Just check at 0
				mCurrentAssignment[mainVar] = RAN(0);
				RAN value = carl::evaluate(helpers.mPool->get(constraint), mCurrentAssignment).value();
				//Reset the assignment
				SMTRAT_LOG_DEBUG("smtrat.covering", "No roots, evaluation at 0 got: " << value);

				if (wasSet) {
					mCurrentAssignment[mainVar] = oldValue;
				} else {
					mCurrentAssignment.erase(mainVar);
				}

				if (carl::compare(value, mpq_class(0), carl::Relation::LESS)) {
					//True case
					continue; //Algo line 9
				} else {
					//False case ;
					result.push_back(CellInformation{LowerBound{std::nullopt, true}, UpperBound{std::nullopt, true}, {constraint}, {}, {}, {}});
					return result; //Algo line 7
				}
			}

			//Todo: Use proper infeasible intervals and bound types
			//Todo: Think about how to clean up the following code
			//Todo: Polynomial simplifications of section 4.4.3 (they are already normalized but not square free -> to that in PolyRefVector::add?)

			RAN value;
			//Algo line 11 and following
			//Add (-infty, roots[0])
			mCurrentAssignment[mainVar] = carl::sample_below(roots.front());
			value = carl::evaluate(helpers.mPool->get(constraint), mCurrentAssignment).value();
			SMTRAT_LOG_DEBUG("smtrat.covering", "Evaluation at " << mCurrentAssignment << " got: " << value);
			if (!carl::compare(value, mpq_class(0), carl::Relation::LESS)) {
				//If constraint evaluates to false
				result.push_back(CellInformation{LowerBound{std::nullopt, true}, UpperBound{roots.front(), true}, {constraint}, {}, {}, {constraint}});
				SMTRAT_LOG_DEBUG("smtrat.covering", "Adding: " << result.back());
			}

			//add [roots[0], roots[0]]
			mCurrentAssignment[mainVar] = roots.front();
			value = carl::evaluate(helpers.mPool->get(constraint), mCurrentAssignment).value();
			SMTRAT_LOG_DEBUG("smtrat.covering", "Evaluation at " << mCurrentAssignment << " got: " << value);
			if (!carl::compare(value, mpq_class(0), carl::Relation::LESS)) {
				//If constraint evaluates to false
				result.push_back(CellInformation{LowerBound{roots.front(), false}, UpperBound{roots.front(), false}, {constraint}, {}, {constraint}, {constraint}});
				SMTRAT_LOG_DEBUG("smtrat.covering", "Adding: " << result.back());
			}

			for (std::size_t i = 0; i < roots.size() - 1; i++) {
				//add (roots[i], roots[i+1])
				mCurrentAssignment[mainVar] = carl::sample_between(roots[i], roots[i + 1]);
				value = carl::evaluate(helpers.mPool->get(constraint), mCurrentAssignment).value();
				SMTRAT_LOG_DEBUG("smtrat.covering", "No roots, evaluation at " << mCurrentAssignment << " got: " << value);
				if (!carl::compare(value, mpq_class(0), carl::Relation::LESS)) {
					//If constraint evaluates to false
					result.push_back(CellInformation{LowerBound{roots[i], true}, UpperBound{roots[i + 1], true}, {constraint}, {}, {}, {constraint}});
					SMTRAT_LOG_DEBUG("smtrat.covering", "Adding: " << result.back());
				}
				//add [roots[i+1], roots[i+1]]
				mCurrentAssignment[mainVar] = roots[i + 1];
				value = carl::evaluate(helpers.mPool->get(constraint), mCurrentAssignment).value();
				SMTRAT_LOG_DEBUG("smtrat.covering", "Evaluation at " << mCurrentAssignment << " got: " << value);
				if (!carl::compare(value, mpq_class(0), carl::Relation::LESS)) {
					//If constraint evaluates to false
					result.push_back(CellInformation{LowerBound{roots[i + 1], false}, UpperBound{roots[i + 1], false}, {constraint}, {}, {}, {constraint}});
					SMTRAT_LOG_DEBUG("smtrat.covering", "Adding: " << result.back());
				}
			}

			//Add (roots[roots.size()], infty])
			mCurrentAssignment[mainVar] = carl::sample_above(roots.back());
			value = carl::evaluate(helpers.mPool->get(constraint), mCurrentAssignment).value();
			SMTRAT_LOG_DEBUG("smtrat.covering", "Evaluation at " << mCurrentAssignment << " got: " << value);
			if (!carl::compare(value, mpq_class(0), carl::Relation::LESS)) {
				//If constraint evaluates to false
				result.push_back(CellInformation{LowerBound{roots.back(), true}, UpperBound{std::nullopt, true}, {constraint}, {}, {constraint}, {}});
				SMTRAT_LOG_DEBUG("smtrat.covering", "Adding: " << result.back());
			}

			//Set Assignment to before state
			if (wasSet) {
				mCurrentAssignment[mainVar] = oldValue;
			} else {
				mCurrentAssignment.erase(mainVar);
			}
		}

		SMTRAT_LOG_DEBUG("smtrat.covering", "Found Unsat Intervals: " << result);
		return result;
	}

	Answer getUnsatCover(const std::size_t level) {
		SMTRAT_LOG_DEBUG("smtrat.covering", " getUnsatCover for level: " << level << " with current assignment: " << mCurrentAssignment);
		std::vector<CellInformation> cells = getUnsatIntervals(level);
		mCoveringInformation[level].insert(mCoveringInformation[level].end(), cells.begin(), cells.end());
		orderAndCleanIntervals(mCoveringInformation[level]);
		RAN sample;
		while (sampleOutside(mCoveringInformation[level], sample)) {
			mCurrentAssignment[mVariableOrdering[level]] = sample;
			if (level + 1 == mVariableOrdering.size()) { //Size is one higher than level because we start at level 0
				//sample is full dimensional -> return SAT
				SMTRAT_LOG_DEBUG("smtrat.covering", "Found satisfying assignment: " << mCurrentAssignment);
				return Answer::SAT;
			}
			Answer recursiveCall = getUnsatCover(level + 1);
			if (recursiveCall == Answer::SAT) {
				return Answer::SAT;
			}
			PolyRefVector characterization = constructCharacterization(level);
			mCurrentAssignment.erase(mVariableOrdering[level]);
			CellInformation interval = intervalFromCharacterization(characterization, sample, level);
			SMTRAT_LOG_DEBUG("smtrat.covering", "Found Unsat Interval: " << interval);

			//todo: Add directly into the correct position according to interval ordering
			mCoveringInformation[level].push_back(interval);
			SMTRAT_LOG_DEBUG("smtrat.covering", "New Unsat Intervals: " << mCoveringInformation[level] << " for sample: " << sample);

			//delete stored information of next higher dimension
			mCoveringInformation[level + 1].clear();
		}
		if (level + 1 != mVariableOrdering.size()) mCoveringInformation[level + 1].clear(); //Todo is that necessary?
		return Answer::UNSAT;
	}

	~Backend() {
	}
};
} // namespace smtrat
