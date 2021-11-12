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

//Use lowest degree barier

using namespace cadcells;

template<typename Settings>
class Backend {
	using SettingsT = Settings;

private:
	//Variable Ordering
	std::vector<carl::Variable> mVariableOrdering;

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

	//Current Covering Information, only contains partial coverings
	std::vector<std::vector<datastructures::SampledDerivationRef<PropSet>>> mCoveringInformation;

	//Levelwise Mapping from derivation to its resulting constraint
	std::map<datastructures::SampledDerivationRef<PropSet>, ConstraintT> mDerivationToConstraint;

	//Infeasible subsets, contains levelwise all constraints which resulted in a complete covering
	std::vector<boost::container::flat_set<ConstraintT>> mInfeasibleSubsets;

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
		mInfeasibleSubsets.resize(varOrdering.size());
	}

	size_t dimension() {
		return mVariableOrdering.size();
	}

	const carl::ran_assignment<Rational>& getCurrentAssignment() {
		return mCurrentAssignment;
	}

	const auto& getCoveringInformation() {
		return mCoveringInformation;
	}

	//TODO: The reasons from constructCharacterization are not added yet!!
	FormulaSetT getInfeasibleSubset(){
		FormulaSetT infeasibleSubset;
		for (const auto& infeasibleSubsetLevel : mInfeasibleSubsets) {
			for (const auto& infeasibleSubsetConstraint : infeasibleSubsetLevel) {
				infeasibleSubset.insert(FormulaT(infeasibleSubsetConstraint));
			}
		}
		return infeasibleSubset;
	}

	//Adds a constraint into the right level
	void addConstraint(const ConstraintT& constraint) {
		//We can substract 1 from level because we dont have constant polynomials
		std::size_t level = helper::level_of(mVariableOrdering, constraint.lhs()) - 1;
		SMTRAT_LOG_DEBUG("smtrat.covering", "Adding Constraint : " << constraint << " on level " << level);
		mUnknownConstraints[level].insert(constraint);
	}

	auto& getUnknownConstraints() {
		return mUnknownConstraints;
	}

	auto& getKnownConstraints() {
		return mKnownConstraints;
	}

	//Delete all stored data with level higher or equal
	void resetStoredData(std::size_t level) {
		for (size_t i = level; i < dimension(); i++) {
			//Resetting the covering data
			mCoveringInformation[i].clear();
			//Resetting the infeasible subsets
			mInfeasibleSubsets[i].clear();
			//Resetting the assignment
			mCurrentAssignment.erase(mVariableOrdering[i]);
			//Resetting the known constraints
			for (const auto& constraint : mKnownConstraints[i]) {
				mUnknownConstraints[i].insert(std::move(constraint));
			}
			mKnownConstraints[i].clear();
		}
	}

	void removeConstraint(const ConstraintT& constraint) {
		//We can substract 1 from level because we dont have constant polynomials
		std::size_t level = helper::level_of(mVariableOrdering, constraint.lhs()) - 1;
		SMTRAT_LOG_DEBUG("smtrat.covering", "Removing Constraint : " << constraint << " on level " << level);

		//If we find the constraint in the unknown constraints we have the easy case -> Just remove it and not care about the stored data
		//Is that case even possible?
		if (mUnknownConstraints[level].find(constraint) != mUnknownConstraints[level].end()) {
			mUnknownConstraints[level].erase(constraint);
			SMTRAT_LOG_DEBUG("smtrat.covering", "Constraint to remove was in unknown constraints");
			return;
		}

		//The hard case -> The constraint must be in the known constraints
		//We have to remove it and remove all the stored data that originated from this constraint
		assert(mKnownConstraints[level].find(constraint) != mKnownConstraints[level].end());
		mKnownConstraints[level].erase(constraint);
		//TODO
		return;
	}

	void filterAndStoreDerivations(const datastructures::CoveringRepresentation<PropSet>& mCovering, const std::size_t& level) {
		//Safe the derivations for the level
		//We only need the derivations used in the current (partial) Covering
		mCoveringInformation[level].clear();
		for (const auto& cell : mCovering.cells) {
			mCoveringInformation[level].push_back(cell.derivation);
		}
	}

	void setConstraintsKnown(const std::size_t& level) {
		for (const auto& constraint : mUnknownConstraints[level]) {
			mKnownConstraints[level].insert(std::move(constraint));
		}
		mUnknownConstraints[level].clear();
	}

	//Todo: Only delete the one level and not also all higher ones?
	void setConstraintsUnknown(const std::size_t& level) {
		//Set the constraints of the given level and all higher dimensions to be unknown.
		for (std::size_t i = level; i < mVariableOrdering.size(); i++) {
			for (const auto& constraint : mKnownConstraints[i]) {
				mUnknownConstraints[i].insert(std::move(constraint));
			}
			mKnownConstraints[i].clear();
		}
	}

	Answer getUnsatCover(const std::size_t level) {
		SMTRAT_LOG_DEBUG("smtrat.covering", " getUnsatCover for level: " << level << " with current assignment: " << mCurrentAssignment);
		SMTRAT_LOG_DEBUG("smtrat.covering", " Variable Ordering: " << mVariableOrdering);
		SMTRAT_LOG_DEBUG("smtrat.covering", " Dimension: " << dimension());
		SMTRAT_LOG_DEBUG("smtrat.covering", " Unknown Constraints: " << mUnknownConstraints);
		std::vector<datastructures::SampledDerivationRef<PropSet>> unsat_cells;
		for (const ConstraintT& constraint : mUnknownConstraints[level]) {

			SMTRAT_LOG_DEBUG("smtrat.covering", "Checking constraint: " << constraint);
			SMTRAT_LOG_DEBUG("smtrat.covering", "Current Assignment size: " << mCurrentAssignment.size());
			SMTRAT_LOG_DEBUG("smtrat.covering", "Current level: " << level);
			SMTRAT_LOG_DEBUG("smtrat.covering", "Level of constraint: " << helper::level_of(mVariableOrdering, constraint.lhs()));
			SMTRAT_LOG_DEBUG("smtrat.covering", " Variable Ordering: " << mVariableOrdering);
			SMTRAT_LOG_DEBUG("smtrat.covering", "Projection Variable Ordering: " << mProjections->polys().var_order());

			auto intervals = algorithms::get_unsat_intervals<op>(constraint, *mProjections, mCurrentAssignment);
			//TODO: Map von sampled deriv zu constraints für infeasible subset, Alle constraints die irgendwie eine derivation erzeugt haben
			for (const auto& interval : intervals) {
				SMTRAT_LOG_DEBUG("smtrat.covering", "Found UNSAT Interval: " << interval->cell() << "  from constraint: " << constraint);
				//Insert into the derivation to constraint map
				mDerivationToConstraint.insert(std::make_pair(interval, constraint));
			}
			unsat_cells.insert(unsat_cells.end(), intervals.begin(), intervals.end());
		}

		//Set the unknown constraints to be known, as all new derivations have been calculated
		setConstraintsKnown(level);

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
				SMTRAT_LOG_DEBUG("smtrat.covering", "Found satisfying variable assignment: " << mCurrentAssignment);
				return Answer::SAT;
			}

			Answer nextLevel = getUnsatCover(level + 1);

			if (nextLevel == Answer::SAT) {
				//Push down SAT
				return nextLevel;
			} else if (nextLevel == Answer::UNSAT) {
				//NextLevel is Unsat -> Generate Unsat-Cell
				//Todo: how to get the constraints which resulted in the unsat-cell for the infeasible subset?
				SMTRAT_LOG_DEBUG("smtrat.covering", "Last full covering: " << mLastFullCovering);

				auto cell_derivs = mLastFullCovering.sampled_derivations();
				datastructures::merge_underlying(cell_derivs);
				operators::project_covering_properties<op>(mLastFullCovering);
				auto new_deriv = mLastFullCovering.cells.front().derivation->underlying().sampled_ref();
				if (!operators::project_cell_properties<op>(*new_deriv)) {
					SMTRAT_LOG_TRACE("smtrat.covering", "Could not project properties");
					return Answer::UNKNOWN;
				}
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

				//delete the now obsolete variable assignment
				mCurrentAssignment.erase(mVariableOrdering[level]);
			} else {
				//Something went wrong (McCallum failed)
				return Answer::UNKNOWN;
			}
		}

		SMTRAT_LOG_DEBUG("smtrat.covering", "Cells cover the numberline ");
		//operators::project_covering_properties<op>(mCurrentCovering.value());
		mLastFullCovering = std::move(mCurrentCovering.value());
		//Remove the stored covering information
		mCoveringInformation[level].clear();
		setConstraintsUnknown(level);

		//Construct the infeasible subset for the current level
		//First reset the stored infeasible subset if there is one 
		mInfeasibleSubsets[level].clear();
		//now add the constraints which resulted in the unsat-cells of full covering of this level 
		for (const auto& unsat_derivation : mLastFullCovering.sampled_derivation_refs()) {
			//only insert constraints from derivations which where created 
			if(mDerivationToConstraint.find(unsat_derivation) != mDerivationToConstraint.end()) {
				mInfeasibleSubsets[level].insert(mDerivationToConstraint.at(unsat_derivation));
				SMTRAT_LOG_DEBUG("smtrat.covering", "Added constraint " << mDerivationToConstraint.at(unsat_derivation) << " to infeasible subset");
			}else{
				SMTRAT_LOG_DEBUG("smtrat.covering", "Could not find constraint for derivation " << unsat_derivation);
			}
		}

		return Answer::UNSAT;
	}

	~Backend() {
	}
};
} // namespace smtrat
