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

#include "LevelWiseInformation.h"
#include "NewCoveringModule.h"
#include "NewCoveringSettings.h"

#include <smtrat-cadcells/algorithms/unsat_intervals.h>
#include <smtrat-cadcells/helper.h>

namespace smtrat {

using namespace cadcells;

template<typename Settings>
class Backend {


static constexpr cadcells::operators::op op = Settings::op;
using PropSet = typename operators::PropertiesSet<Settings::op>::type;


private:
	// Variable Ordering
	std::vector<carl::Variable> mVariableOrdering;

	// Ordered List of unique unknown Constraints (flat_set by level)
	std::vector<boost::container::flat_set<ConstraintT>> mUnknownConstraints;

	// Ordered List of unique known Constraints (flat_set by level)
	std::vector<boost::container::flat_set<ConstraintT>> mKnownConstraints;

	// Cache for Polynomials
	std::shared_ptr<datastructures::PolyPool> mPool;

	// Cache for polynomial computations
	std::shared_ptr<datastructures::Projections> mProjections;

	// Current (partial) satisfying assignment
	carl::ran_assignment<Rational> mCurrentAssignment;

	// Current Covering Information, only contains partial coverings
	std::vector<LevelWiseInformation<Settings>> mCoveringInformation;

	// Mapping from derivation to the constraints which resulted in its creation
	std::map<datastructures::SampledDerivationRef<PropSet>, std::vector<ConstraintT>> mDerivationToConstraint;

public:
	// Init with empty variable ordering
	Backend() {
		SMTRAT_LOG_DEBUG("smtrat.covering", " Dry Init of Covering Backend");
	}

	// Set Variable Ordering and init cache helpers
	void init(std::vector<carl::Variable>& varOrdering) {
		mVariableOrdering = varOrdering;

		// init Helpers
		mPool = std::make_shared<datastructures::PolyPool>(mVariableOrdering);
		mProjections = std::make_shared<datastructures::Projections>(*mPool);

		// Reserve space for the data structures
		mUnknownConstraints.resize(varOrdering.size());
		mKnownConstraints.resize(varOrdering.size());
		mCoveringInformation.resize(varOrdering.size());
	}

	std::size_t dimension() {
		return mVariableOrdering.size();
	}

	const carl::ran_assignment<Rational>& getCurrentAssignment() {
		return mCurrentAssignment;
	}

	auto& getCoveringInformation() {
		return mCoveringInformation;
	}

	inline FormulaSetT getInfeasibleSubset() {
		assert(mCoveringInformation[0].isFullCovering()) ;

		SMTRAT_LOG_DEBUG("smtrat.covering", "getInfeasibleSubset");
		FormulaSetT infeasibleSubset;
		// We can just take the constraints used in level 0, as all the constraints of higher levels get pushed down if used in the covering
		for (auto& infeasibleConstraint : mCoveringInformation[0].getConstraintsOfCovering(mDerivationToConstraint)) {
			infeasibleSubset.insert(FormulaT(infeasibleConstraint));
		}
		SMTRAT_LOG_DEBUG("smtrat.covering", "getInfeasibleSubset done: " << infeasibleSubset);
		return infeasibleSubset;
	}

	// Adds a constraint into the right level
	void addConstraint(const ConstraintT& constraint) {
		// We can substract 1 from level because we dont have constant polynomials
		std::size_t level = helper::level_of(mVariableOrdering, constraint.lhs()) - 1;
		SMTRAT_LOG_DEBUG("smtrat.covering", "Adding Constraint : " << constraint << " on level " << level);
		mUnknownConstraints[level].insert(constraint);
	}

	auto& getUnknownConstraints() {
		return mUnknownConstraints;
	}

	auto& getUnknownConstraints(std::size_t& level) {
		return mUnknownConstraints[level];
	}

	auto& getKnownConstraints() {
		return mKnownConstraints;
	}

	auto& getKnownConstraints(std::size_t& level) {
		return mKnownConstraints[level];
	}

	void updateAssignment(std::size_t level){
		mCurrentAssignment[mVariableOrdering[level]] = mCoveringInformation[level].getSampleOutside();
	}

	// Delete all stored data with level higher or equal
	void resetStoredData(std::size_t level) {
		if(level == 0){
			resetDerivationToConstraintMap();
		}
		for (std::size_t i = level; i < dimension(); i++) {
			// Resetting the covering data
			mCoveringInformation[i].clear();
			// Resetting the assignment
			mCurrentAssignment.erase(mVariableOrdering[i]);
			// Resetting the known constraints
			for (const auto& constraint : mKnownConstraints[i]) {
				mUnknownConstraints[i].insert(std::move(constraint));
			}
			mKnownConstraints[i].clear();
		}
	}

	void resetDerivationToConstraintMap(){
		mDerivationToConstraint.clear();
	}

	// Return true if the constraint to remove was used in the current covering
	void removeConstraint(const ConstraintT& constraint) {
		// We can substract 1 from level because we dont have constant polynomials
		std::size_t level = helper::level_of(mVariableOrdering, constraint.lhs()) - 1;
		SMTRAT_LOG_DEBUG("smtrat.covering", "Removing Constraint : " << constraint << " on level " << level);
		SMTRAT_LOG_DEBUG("smtrat.covering", "Known Constraints: " << mKnownConstraints);
		SMTRAT_LOG_DEBUG("smtrat.covering", "Unknown Constraints: " << mUnknownConstraints);

		// If we find the constraint in the unknown constraints we have the easy case -> Just remove it and not care about the stored data
		if (mUnknownConstraints[level].find(constraint) != mUnknownConstraints[level].end()) {
			//remove all stored information which resulted from the constraint
			for (std::size_t cur_level = 0; cur_level <= level; cur_level++) {
			mCoveringInformation[cur_level].removeConstraint(constraint, mDerivationToConstraint);
			}
			mUnknownConstraints[level].erase(constraint);
			SMTRAT_LOG_DEBUG("smtrat.covering", "Constraint to remove was in unknown constraints");
			return;
		}

		if(mKnownConstraints[level].find(constraint) == mKnownConstraints[level].end()){
			SMTRAT_LOG_DEBUG("smtrat.covering", "Constraint to remove was not in known constraints");
			//This can happen if the constraint is to be added in the same iteration
			//TODO: what to do then?
			return;
		}

		// The constraint must be in the known constraints
		// remove all stored information which resulted from the constraint
		for (std::size_t cur_level = 0; cur_level <= level; cur_level++) {
			mCoveringInformation[cur_level].removeConstraint(constraint, mDerivationToConstraint);
		}

		// remove the constraint from the known constraints
		mKnownConstraints[level].erase(constraint);
	}

	void setConstraintsKnown(const std::size_t& level) {
		for (const auto& constraint : mUnknownConstraints[level]) {
			mKnownConstraints[level].insert(std::move(constraint));
		}
		mUnknownConstraints[level].clear();
	}

	void setConstraintsUnknown(const std::size_t& level) {
		for (const auto& constraint : mKnownConstraints[level]) {
			mUnknownConstraints[level].insert(std::move(constraint));
		}
		mKnownConstraints[level].clear();
	}

	void processUnknownConstraints(const std::size_t& level) {
		for (const ConstraintT& constraint : mUnknownConstraints[level]) {
			auto intervals = algorithms::get_unsat_intervals<op>(constraint, *mProjections, mCurrentAssignment);
			for (const auto& interval : intervals) {
				SMTRAT_LOG_DEBUG("smtrat.covering", "Found UNSAT Interval: " << interval->cell() << "  from constraint: " << constraint);
				// Insert into the derivation to constraint map
				mDerivationToConstraint.insert(std::make_pair(interval, std::vector<ConstraintT>{constraint}));
			}
			mCoveringInformation[level].addDerivations(std::move(intervals));
		}

		// Set the unknown constraints to be known, as all new derivations have been calculated
		setConstraintsKnown(level);
	}

	Answer getUnsatCover(const std::size_t level) {
		SMTRAT_LOG_DEBUG("smtrat.covering", " getUnsatCover for level: " << level << " / " << dimension());
		SMTRAT_LOG_DEBUG("smtrat.covering", " Variable Ordering: " << mVariableOrdering);
		SMTRAT_LOG_DEBUG("smtrat.covering", " Unknown Constraints: " << mUnknownConstraints);
		SMTRAT_LOG_DEBUG("smtrat.covering", " Current Covering Information: " << mCoveringInformation[level]);

		// incase of incremental solving, we need to check if the current level is already assigned
		// if it is assigned, the current assignment is satisfying all unknown constraints and we dont need to process the unknown constraints
		if (mCurrentAssignment.find(mVariableOrdering[level]) == mCurrentAssignment.end()) {
			processUnknownConstraints(level);
		}

		SMTRAT_LOG_DEBUG("smtrat.covering", "Computing covering representation");
		mCoveringInformation[level].computeCovering();
		SMTRAT_LOG_DEBUG("smtrat.covering", "Got CoveringStatus: " << mCoveringInformation[level].getCoveringStatus());
		if (mCoveringInformation[level].isFailedCovering()) {
			SMTRAT_LOG_DEBUG("smtrat.covering", "Covering failed -> Abort");
			return Answer::UNKNOWN;
		}

		SMTRAT_LOG_DEBUG("smtrat.covering", "Got covering " << mCoveringInformation[level].getCovering());

		while (mCoveringInformation[level].isPartialCovering()) {
			SMTRAT_LOG_DEBUG("smtrat.covering", "Sample outside " << mCoveringInformation[level].getSampleOutside());
			updateAssignment(level);
			if (mCurrentAssignment.size() == mVariableOrdering.size()) {
				// SAT
				SMTRAT_LOG_DEBUG("smtrat.covering", "Found satisfying variable assignment: " << mCurrentAssignment);
				return Answer::SAT;
			}

			Answer nextLevelAnswer = getUnsatCover(level + 1);

			if (nextLevelAnswer == Answer::SAT) {
				// Push down SAT
				return nextLevelAnswer;
			} else if (nextLevelAnswer == Answer::UNSAT) {
		
				auto new_derivation = mCoveringInformation[level+1].constructDerivation(mDerivationToConstraint);
				
				if(!new_derivation.has_value()){
					SMTRAT_LOG_DEBUG("smtrat.covering", "No new derivation found -> Abort");
					return Answer::UNKNOWN;
				}

				SMTRAT_LOG_DEBUG("smtrat.covering", "Found new derivation: " << new_derivation.value()->cell());
				SMTRAT_LOG_DEBUG("smtrat.covering", "Adding new derivation to Covering Information");
				mCoveringInformation[level].addDerivation(std::move(new_derivation.value()));


				// delete the now obsolete data
				mCurrentAssignment.erase(mVariableOrdering[level]);
				mCoveringInformation[level + 1].clear();
				setConstraintsUnknown(level+1);

				// If there are unknown constraints on this level, we need to process them now
				processUnknownConstraints(level);

				// Recalculate the current covering
				SMTRAT_LOG_DEBUG("smtrat.covering", "Computing covering representation");
				mCoveringInformation[level].computeCovering();
				SMTRAT_LOG_DEBUG("smtrat.covering", "Got CoveringStatus: " << mCoveringInformation[level].getCoveringStatus());
				if (mCoveringInformation[level].isFailedCovering()) {
					SMTRAT_LOG_DEBUG("smtrat.covering", "Covering failed -> Abort");
					return Answer::UNKNOWN;
				}

			} else {
				// Something went wrong (McCallum failed)
				return Answer::UNKNOWN;
			}
		}

		assert(mCoveringInformation[level].isFullCovering());
		SMTRAT_LOG_DEBUG("smtrat.covering", "Cells cover the numberline ");

		return Answer::UNSAT;
	}
};
} // namespace smtrat
