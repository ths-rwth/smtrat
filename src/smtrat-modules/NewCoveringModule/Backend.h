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

	//Cache for the last (full) covering
	datastructures::CoveringRepresentation<PropSet> mLastFullCovering;

	//Current Covering Information
	std::vector<std::vector<datastructures::SampledDerivationRef<PropSet>>> mCoveringInformation;

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

	const carl::ran_assignment<Rational>& getCurrentAssignment() {
		return mCurrentAssignment;
	}

	//Adds a constraint into the right level
	void addConstraint(const ConstraintT& constraint) {
		//We can substract 1 from level because we dont have constant polynomials
		std::size_t level = helper::level_of(mVariableOrdering, constraint.lhs()) - 1;
		SMTRAT_LOG_DEBUG("smtrat.covering", "Adding Constraint : " << constraint << " on level " << level);
		mUnknownConstraints[level].insert(constraint);
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

	void filterAndStoreDerivations(const datastructures::CoveringRepresentation<PropSet>& mCovering, const std::size_t& level) {
		//Safe the derivations for the level
		//We only need the derivations used in the current (partial) Covering
		mCoveringInformation[level].clear();
		for (const auto& cell : mCovering.cells) {
			mCoveringInformation[level].push_back(cell.derivation);
		}
	}

	Answer getUnsatCover(const std::size_t level) {
		SMTRAT_LOG_DEBUG("smtrat.covering", " getUnsatCover for level: " << level << " with current assignment: " << mCurrentAssignment);
		SMTRAT_LOG_DEBUG("smtrat.covering", " Variable Ordering: " << mVariableOrdering);
		SMTRAT_LOG_DEBUG("smtrat.covering", " Dimension: " << dimension());
		SMTRAT_LOG_DEBUG("smtrat.covering", " Unknown Constraints: " << mUnknownConstraints);
		//Todo Add UnknownConstraints to Known constraints once the derivations exits
		std::vector<datastructures::SampledDerivationRef<PropSet>> unsat_cells;
		for (const ConstraintT& constraint : mUnknownConstraints[level]) {
			auto intervals = algorithms::get_unsat_intervals<op>(constraint, *mProjections, mCurrentAssignment);
			//TODO: Map von sampled deriv zu constraints für infeasible subset, Alle constraints die irgendwie eine derivation erzeugt haben
			for (const auto& interval : intervals) {
				SMTRAT_LOG_DEBUG("smtrat.covering", "Found UNSAT Interval: " << interval->cell() << "  from constraint: " << constraint);
			}
			unsat_cells.insert(unsat_cells.end(), intervals.begin(), intervals.end());
		}

		//Add stored cells to unsat_cells to compute covering of all known cells
		for (const datastructures::SampledDerivationRef<PropSet>& deriv : mCoveringInformation[level]) {
			unsat_cells.push_back(deriv);
		}

		SMTRAT_LOG_DEBUG("smtrat.covering", "Found unsat cells: " << unsat_cells);

		SMTRAT_LOG_DEBUG("smtrat.covering", "Computing covering representation");
		auto mCurrentCovering = representation::covering<representation::DEFAULT_COVERING>::compute(unsat_cells);
		if (!mCurrentCovering.has_value()) {
			SMTRAT_LOG_DEBUG("smtrat.covering", "McCallum failed -> Aborting");
			return Answer::UNKNOWN;
		}

		//We only need to store the derivations used in the current (partial) covering
		filterAndStoreDerivations(mCurrentCovering.value(), level);
		unsat_cells = mCoveringInformation[level];
		SMTRAT_LOG_DEBUG("smtrat.covering", "Got (partial) covering " << mCurrentCovering);

		RAN sample;
		while (mCurrentCovering.value().sample_outside(sample)) {
			SMTRAT_LOG_DEBUG("smtrat.covering", "Found sample outside " << sample);
			mCurrentAssignment[mVariableOrdering[level]] = sample;
			if (mCurrentAssignment.size() == mVariableOrdering.size()) {
				//SAT
				//We have a full dimensional satisfying assignment
				return Answer::SAT;
			}

			//Make iterative instead of recursion?
			Answer nextLevel = getUnsatCover(level + 1);

			if (nextLevel == Answer::SAT) {
				//Push down SAT
				return nextLevel;
			} else if (nextLevel == Answer::UNSAT) {
				//NextLevel is Unsat -> Generate Unsat-Cell
				SMTRAT_LOG_DEBUG("smtrat.covering", "Last full covering: " << mLastFullCovering);

			    auto cell_derivs = mLastFullCovering.sampled_derivations();
				datastructures::merge_underlying(cell_derivs);
				operators::project_covering_properties<op>(mLastFullCovering);
				auto new_deriv = mLastFullCovering.cells.front().derivation->underlying().sampled_ref();
				operators::project_basic_properties<op>(*new_deriv->delineated());
        		operators::delineate_properties<op>(*new_deriv->delineated());
        		new_deriv->delineate_cell();
				SMTRAT_LOG_DEBUG("smtrat.covering", "Found new unsat cell: " << new_deriv->cell());

				//add new cell to stored data and recalculate the current covering
				unsat_cells.push_back(new_deriv);
				auto newCovering = representation::covering<representation::DEFAULT_COVERING>::compute(unsat_cells);
				if (!newCovering.has_value()) {
					SMTRAT_LOG_DEBUG("smtrat.covering", "McCallum failed -> Aborting");
					return Answer::UNKNOWN;
				} else {
					mCurrentCovering.value().cells = std::move(newCovering.value().cells);
				}
				filterAndStoreDerivations(mCurrentCovering.value(), level);
				unsat_cells = mCoveringInformation[level];

				//delete now obsolete information
				mCurrentAssignment.erase(mVariableOrdering[level]);
				mCoveringInformation[level + 1].clear();
			} else {
				//Something went wrong (McCallum failed)
				return Answer::UNKNOWN;
			}
		}

		SMTRAT_LOG_DEBUG("smtrat.covering", "Cells cover the numberline ");
		//operators::project_covering_properties<op>(mCurrentCovering.value());
		mLastFullCovering = std::move(mCurrentCovering.value());
		return Answer::UNSAT;
	}

	~Backend() {
	}
};
} // namespace smtrat
