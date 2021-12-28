/**
 * @file LevelWiseInformation.h
 * @author Philip Kroll <Philip.Kroll@rwth-aachen.de>
 *
 * @version 2021-12-17
 * Created on 2021-12-17.
 */
#pragma once

#include "NewCoveringModule.h"
#include "NewCoveringSettings.h"
#include <smtrat-cadcells/datastructures/polynomials.h>
#include <smtrat-cadcells/datastructures/projections.h>
#include <smtrat-cadcells/operators/operator_mccallum.h>
#include <smtrat-cadcells/representation/heuristics.h>
#include <smtrat-common/smtrat-common.h>

namespace smtrat {

using namespace smtrat::cadcells;

// Todo: This needs to be read from the passed settings
constexpr auto op = cadcells::operators::op::mccallum;
using PropSet = cadcells::operators::PropertiesSet<op>::type;

// Possible types of covering information
enum CoveringStatus {
	partial = 0,
	full = 1,
	unknown = 2,
	failed = 3,
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

/*
 * @brief The LevelWiseInformation class
 *
 * This class is used to store all calculated information about the given level.
 * This is used for both backtracking,incrementality and caching in general
 */
template<typename Settings>
class LevelWiseInformation {

private:
	// All Information that has been gathered for this level
	std::vector<datastructures::SampledDerivationRef<PropSet>> mDerivations;

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
		mDerivations.push_back(derivation);
	}

	// move in a new derivation
	void addDerivation(datastructures::SampledDerivationRef<PropSet>&& derivation) {
		mDerivations.push_back(std::move(derivation));
	}

	// Add a vector of new derivations
	void addDerivations(const std::vector<datastructures::SampledDerivationRef<PropSet>>& derivations) {
		mDerivations.insert(mDerivations.end(), derivations.begin(), derivations.end());
	}

	// Move a vector of new derivations
	void addDerivations(std::vector<datastructures::SampledDerivationRef<PropSet>>&& derivations) {
		mDerivations.insert(mDerivations.end(), std::make_move_iterator(derivations.begin()), std::make_move_iterator(derivations.end()));
	}

	// clear all derivations and the computed covering and set the full covering flag
	void clear() {
		mDerivations.clear();
		mCovering.reset();
		mCoveringStatus = CoveringStatus::unknown;
	}

	// Compute the covering based on the current derivations
	// Also sets the full covering flag and the sample point if the covering is not a full covering
	// TODO: Make type of covering computation dependent on the settings
	void computeCovering() {

		// If there is an already existing covering which is also full, we are done
		if (isFullCovering()) {
			return;
		}
		// We assume that there are new derivations
		SMTRAT_LOG_DEBUG("smtrat.covering", "Computing covering representation");
		mCovering = representation::covering<representation::DEFAULT_COVERING>::compute(mDerivations);
		if (!mCovering.has_value()) {
			SMTRAT_LOG_DEBUG("smtrat.covering", "McCallum failed");
			mCoveringStatus = CoveringStatus::failed;
			return;
		}
		SMTRAT_LOG_DEBUG("smtrat.covering", "Computed Covering: " << mCovering.value());
		// we can convert the return value of sample_outside to CoveringStatus as 0 == partial covering and 1 == full covering
		mCoveringStatus = CoveringStatus(mCovering.value().sample_outside(mSamplePoint));

		SMTRAT_LOG_DEBUG("smtrat.covering", "CoveringStatus: " << mCoveringStatus);
		SMTRAT_LOG_DEBUG("smtrat.covering", "Sample point: " << mSamplePoint);
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

	// Get the current covering
	// Asserts that the covering actually has been computed and is not unknown or failed
	const datastructures::CoveringRepresentation<PropSet>& getCovering() const {
		assert(mCovering.has_value() && mCoveringStatus != CoveringStatus::unknown && mCoveringStatus != CoveringStatus::failed);
		return mCovering.value();
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
		// Should the covering be computed again here?
	}

	// Remove a single derivations
	void removeDerivation(const datastructures::SampledDerivationRef<PropSet>& derivation) {
		SMTRAT_LOG_DEBUG("smtrat.covering", "Removing derivation: " << derivation);
		assert(std::find(mDerivations.begin(), mDerivations.end(), derivation) != mDerivations.end());

		// If the derivation was used in the current covering, we need to reset it and set the flag accordingly
		if (mCovering.has_value()) {
			auto usedDerivations = mCovering.value().sampled_derivation_refs();
			if (std::find(usedDerivations.begin(), usedDerivations.end(), derivation) != usedDerivations.end()) {
				SMTRAT_LOG_DEBUG("smtrat.covering", "Derivation to remove was used in the current covering representation");
				// delete the current covering
				mCovering.reset();
				mCoveringStatus = CoveringStatus::unknown;
			}
		}

		//Now remove the derivation from the list
		mDerivations.erase(std::remove(mDerivations.begin(), mDerivations.end(), derivation), mDerivations.end());
	}

	// Remove a vector of derivations
	void removeDerivation(const std::vector<datastructures::SampledDerivationRef<PropSet>>& derivations) {
		for (const auto& derivation : derivations) {
			removeDerivation(derivation);
		}
	}

	// remove all derivations that were created using the given constraint
	void removeConstraint(const ConstraintT& constraint, const std::map<datastructures::SampledDerivationRef<PropSet>, std::vector<ConstraintT>>& derivationConstraints) {
		SMTRAT_LOG_DEBUG("smtrat.covering", "Removing constraint: " << constraint);
		if (mCovering.has_value()) {
			auto usedDerivations = mCovering.value().sampled_derivation_refs();
			if (std::find_if(usedDerivations.begin(), usedDerivations.end(), [&](const datastructures::SampledDerivationRef<PropSet>& deriv) {
					return std::find(derivationConstraints.at(deriv).begin(), derivationConstraints.at(deriv).end(), constraint) != derivationConstraints.at(deriv).end();
				}) != usedDerivations.end()) {
				SMTRAT_LOG_DEBUG("smtrat.covering", "Constraint to remove was used in the current covering representation");
				// delete the current covering
				mCovering.reset();
				mCoveringStatus = CoveringStatus::unknown;
				;
			}
		}

		// remove all derivations that use the constraint
		mDerivations.erase(std::remove_if(mDerivations.begin(), mDerivations.end(), [&](const datastructures::SampledDerivationRef<PropSet>& deriv) {
							   return std::find(derivationConstraints.at(deriv).begin(), derivationConstraints.at(deriv).end(), constraint) != derivationConstraints.at(deriv).end();
						   }),
						   mDerivations.end());
	}

	// Get the constraints used in the current covering
	// Can only be used for infeasible subset -> so assert that the covering is full and use the last full covering
	std::vector<ConstraintT> getConstraintsOfCovering(std::map<datastructures::SampledDerivationRef<PropSet>, std::vector<ConstraintT>>& mDerivationToConstraint) {
		assert(isFullCovering() && mCovering.has_value());

		std::vector<ConstraintT> constraints;

		for (const auto& derivation : mCovering.value().sampled_derivation_refs()) {
			assert(mDerivationToConstraint.find(derivation) != mDerivationToConstraint.end());
			std::vector<ConstraintT> new_constraints = mDerivationToConstraint[derivation];
			constraints.insert(constraints.end(), new_constraints.begin(), new_constraints.end());
		}

		// remove duplicates of the constraints
		std::sort(constraints.begin(), constraints.end());
		constraints.erase(std::unique(constraints.begin(), constraints.end()), constraints.end());
		return constraints;
	}
};

// override the << operator to print the LevelWiseInformation
template<typename Settings>
inline std::ostream& operator<<(std::ostream& os, const LevelWiseInformation<Settings>& levelWiseInformation) {
	os << "CoveringStatus: " << levelWiseInformation.getCoveringStatus() << std::endl;
	if (levelWiseInformation.isPartialCovering()) {
		os << "SamplePoint: " << levelWiseInformation.getSampleOutside() << std::endl;
	}
	if (levelWiseInformation.isFullCovering() || levelWiseInformation.isPartialCovering()) {
		os << "Covering: " << levelWiseInformation.getCovering() << std::endl;
	}
	return os;
}

} // namespace smtrat