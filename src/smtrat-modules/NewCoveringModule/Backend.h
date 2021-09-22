/**
 * @file Backend.h
 * @author Philip Kroll <Philip.Kroll@rwth-aachen.de>
 *
 * @version 2021-07-08
 * Created on 2021-07-08.
 */

// https://arxiv.org/pdf/2003.05633.pdf

#pragma once

#include <smtrat-cadcells/common.h>

#include "NewCoveringModule.h"
#include "NewCoveringSettings.h"

#include <smtrat-cadcells/algorithms/unsat_intervals.h>
#include <smtrat-cadcells/helper.h>

namespace smtrat {

//Todo put in settings?
constexpr auto op = cadcells::operators::op::mccallum;
using PropSet = cadcells::operators::PropertiesSet<op>::type;

using namespace cadcells;

template<typename Settings>
class Backend {
	using SettingsT = Settings;

private:
	//Variable Ordering
	std::vector<carl::Variable> mVariableOrdering;

	//Main Variables of constraints need to be in the same ordering as the variable ordering
	std::vector<FormulasT> mConstraints; //boost flat_set?

	//Ordered List of unique unknown Constraints (flat_set by level)
	std::vector<boost::container::flat_set<ConstraintT>> mUnknownConstraints;

	//Ordered List of unique known Constraints (flat_set by level)
	std::vector<boost::container::flat_set<ConstraintT>> mKnownConstraints;

	//Cache for Polynomials
	std::shared_ptr<datastructures::PolyPool> mPool;

	//Cache for polynomial computations
	std::shared_ptr<datastructures::Projections> mProjections;

	//Current (partial) satisfying assignment
	carl::ran_assignment<Rational> mCurrentAssignment;

	//Current Covering Information
	std::vector<datastructures::CoveringRepresentation<PropSet>> mCoveringInformation;

public:
	//Init with empty variable ordering
	Backend() {
		SMTRAT_LOG_DEBUG("smtrat.covering", " Dry Init of Covering Backend");
	}

	//Set Variable Ordering and init cache helpers
	void init(std::vector<carl::Variable>& varOrdering) {
		mVariableOrdering = varOrdering;

		//init Helpers
		mPool = std::make_shared<datastructures::PolyPool>(mVariableOrdering);
		mProjections = std::make_shared<datastructures::Projections>(*mPool);

		//Init Constraint sets
		mKnownConstraints.resize(varOrdering.size());
		mUnknownConstraints.resize(varOrdering.size());
		mCoveringInformation.resize(varOrdering.size());
	}

	size_t dimension() {
		return mVariableOrdering.size();
	}

	//Adds a constraint into the right level
	void addConstraint(const ConstraintT& constraint) {
		//We can substract 1 from level because we dont have constant polynomials
		std::size_t level = helper::level_of(mVariableOrdering, constraint.lhs()) - 1;
		SMTRAT_LOG_DEBUG("smtrat.covering", "Adding Constraint : " << constraint << " on level " << level);
		mUnknownConstraints[level].insert(constraint);
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
			//mCoveringInformation.erase(i); TODO
			mCurrentAssignment.erase(mVariableOrdering[i]);
		}
	}

	Answer getUnsatCover(const std::size_t level) {
		SMTRAT_LOG_DEBUG("smtrat.covering", " getUnsatCover for level: " << level << " with current assignment: " << mCurrentAssignment);
		std::vector<datastructures::SampledDerivationRef<PropSet>> unsat_cells;
		for (const ConstraintT& constraint : mUnknownConstraints[level]) {
			auto intervals = algorithms::get_unsat_intervals<op>(constraint, *mProjections, mCurrentAssignment);
			for (const auto& interval : intervals) {
				SMTRAT_LOG_DEBUG("smtrat.covering", "Found UNSAT Interval: " << interval->cell() << "  from constraint: " << constraint);
			}
			unsat_cells.insert(unsat_cells.end(), intervals.begin(), intervals.end());
		}

		//Add stored cells to unsat_cells to compute covering of all known cells
		//for (const auto& cell : mCoveringInformation[level].sampled_derivations()) {
		//	//todo reference_wrapper to shared_pointer?
		//	unsat_cells.push_back(std::make_shared<datastructures::SampledDerivation<PropSet>>(cell.get()));
		//}

		SMTRAT_LOG_DEBUG("smtrat.covering", "Found unsat cells: " << unsat_cells);

		SMTRAT_LOG_DEBUG("smtrat.covering", "Computing covering representation");
		auto covering_repr = representation::covering<representation::DEFAULT_COVERING>::compute(unsat_cells);
		if (!covering_repr) {
			SMTRAT_LOG_DEBUG("smtrat.covering", "McCallum failed -> Aborting");
			assert(false); //McCallum failed -> What do then?
		}

		//Store the new Covering
		mCoveringInformation[level].cells = std::move(covering_repr.value().cells);

		SMTRAT_LOG_DEBUG("smtrat.covering", "Got representation " << mCoveringInformation[level]);

		RAN sample;
		while (mCoveringInformation[level].sample_outside(sample)) {
			SMTRAT_LOG_DEBUG("smtrat.covering", "Found sample outside " << sample);
			mCurrentAssignment[mVariableOrdering[level]] = sample;
			if (level == mVariableOrdering.size()) {
				//SAT
				return Answer::SAT;
			}

			//Make iterative instead of recursion?
			Answer nextLevel = getUnsatCover(level + 1);

			if (nextLevel == Answer::SAT) {
				//Push down SAT
				return nextLevel;
			} else if (nextLevel == Answer::UNSAT) {
				//NextLevel is Unsat -> Generate Unsat-Cell
				SMTRAT_LOG_DEBUG("smtrat.covering", "Got covering for the next level: " << mCoveringInformation[level + 1]);
				operators::project_covering_properties(mCoveringInformation[level + 1]);
				//operators::delineate_properties<op>(mCoveringInformation[level + 1].delineated()); //construct characterization
				//auto cell = mCoveringInformation[level + 1]->delineate_cell();					   //interval from characterization
				//SMTRAT_LOG_DEBUG("smtrat.covering", "Found UnsatCell: " << cell);
				assert(false);

			} else {
				assert(false);
				return Answer::UNKNOWN;
			}
		}

		SMTRAT_LOG_DEBUG("smtrat.covering", "Cells cover the numberline ");
		return Answer::UNSAT;
	}

	~Backend() {
	}
};
} // namespace smtrat
