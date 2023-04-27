/**
 * @file LevelWiseInformation.h
 * @author Philip Kroll <Philip.Kroll@rwth-aachen.de>
 * Created on 2021-12-17.
 */
#pragma once

#include "Helper.h"
#include "NewCoveringModule.h"
#include "NewCoveringSettings.h"
#include "NewCoveringStatistics.h"
#include <smtrat-cadcells/datastructures/polynomials.h>
#include <smtrat-cadcells/datastructures/projections.h>
#include <smtrat-cadcells/operators/operator_mccallum.h>
#include <smtrat-cadcells/representation/heuristics.h>
#include <smtrat-common/smtrat-common.h>

namespace smtrat {

using namespace cadcells;

// Possible types of covering information
enum CoveringStatus {
	partial = 0,
	full = 1,
	unknown = 2,
	failed = 3,
};

/*
 * @brief The LevelWiseInformation class
 *
 * This class is used to store all calculated information about the given level.
 * This is used for both backtracking, incrementality and caching in general
 * We also store a flag to indicate the known status of the level.
 * Additionally, if the level is not full, we store and compute the sample point outside of the cells.
 * What covering heuristic is to be used is read from the settings.
 */
template<class Settings>
class LevelWiseInformation {

	// get the covering heuristic from the settings
	static constexpr cadcells::representation::CoveringHeuristic covering_heuristic = Settings::covering_heuristic;
	static constexpr cadcells::operators::op op = Settings::op;
	static constexpr SamplingAlgorithm sampling_algorithm = Settings::sampling_algorithm;
	static constexpr IsSampleOutsideAlgorithm is_sample_outside_algorithm = Settings::is_sample_outside_algorithm;
	using PropSet = typename operators::PropertiesSet<Settings::op>::type;

private:
	// All Information that has been gathered for this level
	// Implicitly uses the defined operator< (std::less)
	std::set<datastructures::SampledDerivationRef<PropSet>, SampledDerivationRefCompare> mDerivations;

	// Do the current set of derivations covering the whole numberline?
	CoveringStatus mCoveringStatus;

	// The Covering based on the current set of derivations
	std::optional<datastructures::CoveringRepresentation<PropSet>> mCovering;

	// sample point outside of the covering if the covering is not a full covering
	RAN mSamplePoint;

public:
	// Constructor
	LevelWiseInformation()
		: mCoveringStatus(CoveringStatus::unknown) {}

	// Move Constructor
	LevelWiseInformation(LevelWiseInformation&& other)
		: mDerivations(std::move(other.mDerivations)),
		  mCoveringStatus(other.mCoveringStatus),
		  mCovering(std::move(other.mCovering)),
		  mSamplePoint(other.mSamplePoint) {}

	// Add a new derivation
	void addDerivation(const datastructures::SampledDerivationRef<PropSet>& derivation) {
		mDerivations.insert(derivation);
	}

	// move in a new derivation
	void addDerivation(datastructures::SampledDerivationRef<PropSet>&& derivation) {
		mDerivations.insert(std::move(derivation));
	}

	const std::set<datastructures::SampledDerivationRef<PropSet>, SampledDerivationRefCompare>& getDerivations() const {
		return mDerivations;
	}

	// clear all derivations and the computed covering and set the full covering flag
	void clear() {
		mDerivations.clear();
		mCovering.reset();
		mCoveringStatus = CoveringStatus::unknown;
	}

	/*
	 * @brief Compute the covering based on the current derivations
	 * Also set the covering flag accordingly and the find a sample point if the covering is not a full covering
	 * @returns True, iff the result invalidates the covering of all higher levels (i.e. if the variable assignment of the current level changes)
	 */
	bool computeCovering(carl::ran_assignment<Rational>& currentAssignment, size_t currentLevel) {

		auto startTime = SMTRAT_TIME_START();

		// If there is an already existing covering which is also full, we are done
		if (isFullCovering()) {
			SMTRAT_TIME_FINISH(getStatistics().timeForComputeCovering(), startTime);
			return false;
		}
		// We assume that there are new derivations

		// If we had a partial covering before, we need to check if the sample point is still outside of the cells
		// If that is the case, we can keep all information is the higher levels
		if (isPartialCovering()) {
			// Checking if the old sample point is still valid, i.e. outside if the all derivations
			if (is_sample_outside<is_sample_outside_algorithm>::is_outside(mSamplePoint, mDerivations)) {
				// The old sample Point is still valid, we are done
				SMTRAT_LOG_DEBUG("smtrat.covering", "Sample " << mSamplePoint << " is still outside of the cells");
				mCoveringStatus = CoveringStatus::partial;
				SMTRAT_TIME_FINISH(getStatistics().timeForComputeCovering(), startTime);
				return false;
			}
			SMTRAT_LOG_DEBUG("smtrat.covering", "Sample " << mSamplePoint << " not outside of the cells anymore");
		}

		//based on the underlying set the vector is already sorted, now remove redundancies of the first kind
	

		// Check if the derivations cover the whole numberline
		//  we can convert the return value of sample_outside to CoveringStatus as 0 == partial covering and 1 == full covering
		mCoveringStatus = CoveringStatus(sampling<sampling_algorithm>::sample_outside(mSamplePoint, mDerivations, currentAssignment, currentLevel));

		if (isPartialCovering()) {
			SMTRAT_TIME_FINISH(getStatistics().timeForComputeCovering(), startTime);
			return true;
		}
		// The cells cover the numberline -> Compute the covering representation
		std::vector<datastructures::SampledDerivationRef<PropSet>> derivationsVector(mDerivations.begin(), mDerivations.end()); // The used cells
		mCovering = representation::covering<covering_heuristic>::compute(derivationsVector);
		if (!mCovering.has_value()) {
			SMTRAT_LOG_DEBUG("smtrat.covering", "Covering with " << representation::get_name(covering_heuristic) << " failed");
			mCoveringStatus = CoveringStatus::failed;
			SMTRAT_TIME_FINISH(getStatistics().timeForComputeCovering(), startTime);
			return true ;
		}
		SMTRAT_STATISTICS_CALL(getStatistics().storeHeuristicUsed(currentLevel));
		SMTRAT_LOG_DEBUG("smtrat.covering", "Computed Covering: " << mCovering.value());
		SMTRAT_TIME_FINISH(getStatistics().timeForComputeCovering(), startTime);
		return true ;
	}

	// Get the current sample point which is outside of the current covering
	const RAN& getSampleOutside() const {
		assert(isPartialCovering());
		return mSamplePoint;
	}

	// Information about the current covering
	bool isPartialCovering() const {
		return mCoveringStatus == CoveringStatus::partial;
	}

	bool isFullCovering() const {
		return mCoveringStatus == CoveringStatus::full;
	}

	bool isUnknownCovering() const {
		return mCoveringStatus == CoveringStatus::unknown;
	}

	bool isFailedCovering() const {
		return mCoveringStatus == CoveringStatus::failed;
	}

	CoveringStatus getCoveringStatus() const {
		return mCoveringStatus;
	}

	// override the =operator to move the current covering
	LevelWiseInformation& operator=(LevelWiseInformation&& other) {
		mCovering = std::move(other.mCovering);
		mDerivations = std::move(other.mDerivations);
		mCoveringStatus = other.mCoveringStatus;
		mSamplePoint = other.mSamplePoint;
		return *this;
	}

	// override the current sampled derivations
	void setDerivations(std::vector<datastructures::SampledDerivationRef<PropSet>>&& derivations) {
		mDerivations = std::move(derivations);

		// this invalides the other stored information
		mCovering.reset();
		mCoveringStatus = CoveringStatus::unknown;
	}

	// Remove a single derivations
	/*
	 * @brief Remove a single derivation from the current set of derivations, if a covering was computed before, and the derivation was used, the covering is invalidated
	 */
	void removeDerivation(const datastructures::SampledDerivationRef<PropSet>& derivation) {
		SMTRAT_LOG_DEBUG("smtrat.covering", "Removing derivation: " << derivation);
		assert(std::find(mDerivations.begin(), mDerivations.end(), derivation) != mDerivations.end());

		// If the derivation was used in the current covering, we need to reset it and set the flag accordingly
		if (mCovering.has_value()) {
			auto usedDerivations = mCovering.value().sampled_derivations();
			if (std::find(usedDerivations.begin(), usedDerivations.end(), derivation) != usedDerivations.end()) {
				SMTRAT_LOG_DEBUG("smtrat.covering", "Derivation to remove was used in the current covering representation");
				// delete the current covering
				mCovering.reset();
				mCoveringStatus = CoveringStatus::unknown;
			}
		}

		// Now remove the derivation from the list
		mDerivations.erase(derivation);
	}

	// Remove a vector of derivations -> Just call removeDerivation for each derivation in the vector
	void removeDerivation(const std::vector<datastructures::SampledDerivationRef<PropSet>>& derivations) {
		for (const auto& derivation : derivations) {
			removeDerivation(derivation);
		}
	}

	/*
	 * @brief Remove all derivations that were created using the given constraint, if a covering was computed before, and the derivation was used, the covering is invalidated
	 */
	void removeConstraint(const ConstraintT& constraint, const std::map<datastructures::SampledDerivationRef<PropSet>, std::vector<ConstraintT>>& derivationConstraints) {
		SMTRAT_LOG_DEBUG("smtrat.covering", "Removing constraint: " << constraint);
		if (mCovering.has_value()) {
			auto usedDerivations = mCovering.value().sampled_derivations();
			if (std::find_if(usedDerivations.begin(), usedDerivations.end(), [&](const datastructures::SampledDerivationRef<PropSet>& deriv) {
					return std::find(derivationConstraints.at(deriv).begin(), derivationConstraints.at(deriv).end(), constraint) != derivationConstraints.at(deriv).end();
				}) != usedDerivations.end()) {
				SMTRAT_LOG_DEBUG("smtrat.covering", "Constraint to remove was used in the current covering representation");
				// delete the current covering
				mCovering.reset();
				mCoveringStatus = CoveringStatus::unknown;
			}
		}

		// remove all derivations that use the constraint
		// TODO: When we switch to C++20, we can use erase_if here
		for (auto it = mDerivations.begin(); it != mDerivations.end();) {
			if (std::find(derivationConstraints.at(*it).begin(), derivationConstraints.at(*it).end(), constraint) != derivationConstraints.at(*it).end()) {
				it = mDerivations.erase(it);
			} else {
				++it;
			}
		}
		// TODO: for memory reasons we could also remove the derivation from the derivationConstraints map -> is this worth it?
	}

	/*
	 * @brief Get the constraints used in the current covering
	 * @return A vector of constraints
	 * @param derivationConstraints A map of derivations to constraints which created it
	 * This can only be used for infeasible subset -> so assert that the covering is full and use the last full covering
	 */
	std::vector<ConstraintT> getConstraintsOfCovering(std::map<datastructures::SampledDerivationRef<PropSet>, std::vector<ConstraintT>>& mDerivationToConstraint) {
		assert(isFullCovering() && mCovering.has_value());

		std::vector<ConstraintT> constraints;
		assert(mCovering.has_value());
		for (const auto& derivation : mCovering.value().sampled_derivations()) {
			assert(mDerivationToConstraint.find(derivation) != mDerivationToConstraint.end());
			std::vector<ConstraintT> new_constraints = mDerivationToConstraint[derivation];
			constraints.insert(constraints.end(), new_constraints.begin(), new_constraints.end());
		}

		// remove duplicates of the constraints
		std::sort(constraints.begin(), constraints.end());
		constraints.erase(std::unique(constraints.begin(), constraints.end()), constraints.end());
		return constraints;
	}

	// Construct a new derivation based on the current covering
	//  Asserts that the covering is full
	/*
	 * @brief Construct a new derivation based on the current covering
	 * @return SampledDerivationRef: Information for the lower dimension, derived from the current covering
	 * @param derivationConstraints A map of derivations to constraints which created it
	 * @note: This represents Section 4.6 in the paper https://arxiv.org/pdf/2003.05633.pdf
	 */
	std::optional<datastructures::SampledDerivationRef<PropSet>> constructDerivation(std::map<datastructures::SampledDerivationRef<PropSet>, std::vector<ConstraintT>>& mDerivationToConstraint) {
		auto startTime = SMTRAT_TIME_START();

		assert(mCovering.has_value());
		assert(isFullCovering());

		auto& fullCovering = mCovering.value();

		SMTRAT_LOG_DEBUG("smtrat.covering", "Got full covering: " << fullCovering);

		auto usedConstraints = getConstraintsOfCovering(mDerivationToConstraint);
		auto cell_derivs = fullCovering.sampled_derivations();
		datastructures::merge_underlying(cell_derivs);
		operators::project_covering_properties<op>(fullCovering);
		datastructures::SampledDerivationRef<PropSet> new_deriv = fullCovering.cells.front().derivation->underlying().sampled_ref();
		if (!operators::project_cell_properties<op>(*new_deriv)) {
			SMTRAT_LOG_DEBUG("smtrat.covering", "Could not project properties");
			SMTRAT_TIME_FINISH(getStatistics().timeForConstructDerivation(), startTime);

			return std::nullopt;
		}
		operators::project_basic_properties<op>(*new_deriv->delineated());
		operators::delineate_properties<op>(*new_deriv->delineated());
		new_deriv->delineate_cell();

		// Update bounds
		if(fullCovering.is_fully_flagged()) {
			bool l = !new_deriv->cell().lower_unbounded();
			bool u = !new_deriv->cell().upper_unbounded();
			
			new_deriv->setEndpoints(l, u);
			new_deriv->set_strictness_of_ancestor_intervals();
		}

		// Get polynomials of constraints
		size_t max_level = 0;
		for(const auto& constraint : usedConstraints) {
			size_t level = helper::level_of(getStatistics().getVariableOrdering(), constraint.lhs()) - 1;
			if(level > max_level) {
				max_level = level;
			}
		}
		SMTRAT_STATISTICS_CALL(getStatistics().levelWiseCreatedInterval(fullCovering.is_fully_flagged(), new_deriv->level(), max_level));


		// Need to update cell bounds
		SMTRAT_LOG_DEBUG("smtrat.covering", "Found new unsat cell for the higher dimension: " << new_deriv->cell());

		// The origin of the new derivation are all constraints used in the last full covering

		mDerivationToConstraint.insert(std::make_pair(new_deriv, usedConstraints));
		SMTRAT_TIME_FINISH(getStatistics().timeForConstructDerivation(), startTime);

		return new_deriv;
	}
};

// override the << operator for CoveringStatus
inline std::ostream& operator<<(std::ostream& os, const CoveringStatus& status) {
	switch (status) {
	case CoveringStatus::partial:
		os << "partial";
		break;
	case CoveringStatus::full:
		os << "full";
		break;
	case CoveringStatus::unknown:
		os << "unknown";
		break;
	case CoveringStatus::failed:
		os << "failed";
		break;
	default:
		os << "unknown";
		break;
	}
	return os;
}

// override the << operator to print the LevelWiseInformation
template<typename Settings>
inline std::ostream& operator<<(std::ostream& os, const LevelWiseInformation<Settings>& levelWiseInformation) {
	os << "CoveringStatus: " << levelWiseInformation.getCoveringStatus() << std::endl;
	if (levelWiseInformation.isPartialCovering()) {
		os << "SamplePoint: " << levelWiseInformation.getSampleOutside() << std::endl;
	}
	if (levelWiseInformation.isFullCovering() || levelWiseInformation.isPartialCovering()) {
		os << "Derivations: " << levelWiseInformation.getDerivations() << std::endl;
	}
	return os;
}

} // namespace smtrat