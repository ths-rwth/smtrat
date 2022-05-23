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

	// Return all constraints that are reason for the derivation used in the full covering on level 0
	inline FormulaSetT getInfeasibleSubset() {
		assert(mCoveringInformation[0].isFullCovering());

		SMTRAT_LOG_DEBUG("smtrat.covering", "getInfeasibleSubset");
		// Use Set to avoid duplicates
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

	// Adds a constraint into the right level, already given the level
	void addConstraint(const size_t level, const std::vector<ConstraintT>&& constraints) {
		SMTRAT_LOG_DEBUG("smtrat.covering", "Adding Constraints : " << constraints << " on level " << level);
		for (const auto& constraint : constraints) {
			assert((helper::level_of(mVariableOrdering, constraint.lhs()) - 1) == level);
			mUnknownConstraints[level].insert(std::move(constraint));
		}
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

	void updateAssignment(std::size_t level) {
		mCurrentAssignment[mVariableOrdering[level]] = mCoveringInformation[level].getSampleOutside();
	}

	// Delete all stored data with level higher or equal
	void resetStoredData(std::size_t level) {
		if (level == 0) {
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

	void resetDerivationToConstraintMap() {
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
			assert(mKnownConstraints[level].find(constraint) == mKnownConstraints[level].end());
			// remove all stored information which resulted from the constraint
			for (std::size_t cur_level = 0; cur_level <= level; cur_level++) {
				SMTRAT_LOG_DEBUG("smtrat.covering", "Removing on level " << cur_level);
				mCoveringInformation[cur_level].removeConstraint(constraint, mDerivationToConstraint);
			}
			mUnknownConstraints[level].erase(constraint);
			SMTRAT_LOG_DEBUG("smtrat.covering", "Constraint to remove was in unknown constraints");
			return;
		}

		if (mKnownConstraints[level].find(constraint) == mKnownConstraints[level].end()) {
			SMTRAT_LOG_DEBUG("smtrat.covering", "Constraint to remove was not in known constraints");
			// This can happen if the constraint is to be added in the same iteration
			// TODO: what to do then?
			return;
		}

		// The constraint must be in the known constraints
		SMTRAT_LOG_DEBUG("smtrat.covering", "Constraint to remove was in known constraints");
		// remove all stored information which resulted from the constraint
		for (std::size_t cur_level = 0; cur_level <= level; cur_level++) {
			SMTRAT_LOG_DEBUG("smtrat.covering", "Removing on level " << cur_level);
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
		// Note: this also resets all higher levels
		for (std::size_t i = level; i < dimension(); i++) {
			for (const auto& constraint : mKnownConstraints[i]) {
				mUnknownConstraints[i].insert(std::move(constraint));
			}
			mKnownConstraints[i].clear();
		}
	}

	void processUnknownConstraints(const std::size_t& level, const bool prune_assignment) {
		SMTRAT_LOG_DEBUG("smtrat.covering", "Processing unknown constraints on level " << level << " with " << mUnknownConstraints[level].size() << " constraints");
		SMTRAT_LOG_DEBUG("smtrat.covering", "Need to prune the assignment: " << prune_assignment);


		for (const ConstraintT& constraint : mUnknownConstraints[level]) {
			std::vector<datastructures::SampledDerivationRef<PropSet>> intervals ;
			if (prune_assignment) {
				intervals = algorithms::get_unsat_intervals<op>(constraint, *mProjections, mCurrentAssignment);
			} else {
				// create copy of the assignment with mVariableOrdering[level] and following not present
				carl::ran_assignment<Rational> assignment;
				for (std::size_t i = 0; i < level; i++) {
					assignment[mVariableOrdering[i]] = mCurrentAssignment[mVariableOrdering[i]];
				}
				intervals = algorithms::get_unsat_intervals<op>(constraint, *mProjections, assignment);
				SMTRAT_LOG_DEBUG("smtrat.covering", "Checking constraint " << constraint << " for unsat intervals yields " << intervals);
			}
			for (const auto& interval : intervals) {
				SMTRAT_LOG_DEBUG("smtrat.covering", "Found UNSAT Interval: " << interval->cell() << "  from constraint: " << constraint);
				// Insert into the derivation to constraint map
				mDerivationToConstraint.insert(std::make_pair(interval, std::vector<ConstraintT>{constraint}));
				mCoveringInformation[level].addDerivation(std::move(interval));
			}
		}

		// Set the unknown constraints to be known, as all new derivations have been calculated
		setConstraintsKnown(level);
	}

	Answer getUnsatCover(const std::size_t level) {
		SMTRAT_LOG_DEBUG("smtrat.covering", " getUnsatCover for level: " << level << " / " << dimension());
		SMTRAT_LOG_DEBUG("smtrat.covering", " Variable Ordering: " << mVariableOrdering);
		SMTRAT_LOG_DEBUG("smtrat.covering", " Unknown Constraints: " << mUnknownConstraints[level]);
		SMTRAT_LOG_DEBUG("smtrat.covering", " Known Constraints: " << mKnownConstraints[level]);
		SMTRAT_LOG_DEBUG("smtrat.covering", " Current Covering Information: " << mCoveringInformation[level]);
		SMTRAT_LOG_DEBUG("smtrat.covering", " Current Assignment: " << mCurrentAssignment);

		// incase of incremental solving, we need to check if the current level is already assigned
		// if it is assigned, the current assignment is satisfying all unknown constraints and we dont need to process the unknown constraints
		// If we know that the assignment is still satisfying we also dont need to recalculate the (partial!) covering.
		if (mCurrentAssignment.find(mVariableOrdering[level]) == mCurrentAssignment.end()) {
			processUnknownConstraints(level, false);
			SMTRAT_LOG_DEBUG("smtrat-covering", "Computing Covering represenentation")
			bool invalidates = mCoveringInformation[level].computeCovering();
			if (invalidates) {
				SMTRAT_LOG_DEBUG("smtrat.covering", "Computed Covering invalidates all higher levels as the underlying sample point changed");
				resetStoredData(level + 1);
			}
		} else {
			SMTRAT_LOG_DEBUG("smtrat.covering", "Current variable " << mVariableOrdering[level] << " is assigned, skipping processing of new constraints and computing covering representation");
			// Possible in the case that SAT was reported before and constraints were removed and invalidated the current partial covering
			if (mCoveringInformation[level].isUnknownCovering()) {
				SMTRAT_LOG_DEBUG("smtrat.covering", "Covering was invalidated, recomputing covering representation and processing all unknown constraints");
				processUnknownConstraints(level, true);
				bool invalidates = mCoveringInformation[level].computeCovering();
				if (invalidates) {
					SMTRAT_LOG_DEBUG("smtrat.covering", "Computed Covering invalidates all higher levels as the underlying sample point changed");
					resetStoredData(level + 1);
				}
				assert(mCoveringInformation[level].isPartialCovering());
			}
		}

		SMTRAT_LOG_DEBUG("smtrat.covering", "Got CoveringStatus: " << mCoveringInformation[level].getCoveringStatus());
		if (mCoveringInformation[level].isFailedCovering()) {
			SMTRAT_LOG_DEBUG("smtrat.covering", "Covering failed -> Abort");
			return Answer::UNKNOWN;
		}

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
				SMTRAT_LOG_DEBUG("smtrat.covering", "Got SAT on level: " << level);
				// Push down SAT
				return nextLevelAnswer;
			} else if (nextLevelAnswer == Answer::UNSAT) {

				auto new_derivation = mCoveringInformation[level + 1].constructDerivation(mDerivationToConstraint);

				if (!new_derivation.has_value()) {
					SMTRAT_LOG_DEBUG("smtrat.covering", "No new derivation found -> Abort");
					return Answer::UNKNOWN;
				}

				// Bounds should be set already
				SMTRAT_LOG_DEBUG("smtrat.covering", "Found new derivation: " << new_derivation.value()->cell());
				SMTRAT_LOG_DEBUG("smtrat.covering", "Adding new derivation to Covering Information");
				mCoveringInformation[level].addDerivation(std::move(new_derivation.value()));

				// delete the now obsolete data
				mCurrentAssignment.erase(mVariableOrdering[level]);
				mCoveringInformation[level + 1].clear();
				setConstraintsUnknown(level + 1);

				// If there are unknown constraints on this level, we need to process them now
				processUnknownConstraints(level, false);

				// Recalculate the current covering
				SMTRAT_LOG_DEBUG("smtrat.covering", "Computing covering representation");
				bool invalidates = mCoveringInformation[level].computeCovering();
				if (invalidates) {
					SMTRAT_LOG_DEBUG("smtrat.covering", "Computed Covering invalidates all higher levels as the underlying sample point changed");
					resetStoredData(level + 1);
				}
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
