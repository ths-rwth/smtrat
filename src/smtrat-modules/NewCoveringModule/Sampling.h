/**
 * @file Sampling.h
 * @author Philip Kroll <Philip.Kroll@rwth-aachen.de>
 * Created on 2022-03-16.
 */
#pragma once

#include "Helper.h"
#include "NewCoveringStatistics.h"
#include <smtrat-cadcells/common.h>
#include <smtrat-cadcells/datastructures/derivation.h>
#include <smtrat-cadcells/datastructures/delineation.h>
#include <smtrat-common/smtrat-common.h>

namespace smtrat {

enum SamplingAlgorithm {
	LOWER_UPPER_BETWEEN_SAMPLING, // First checks lower bound and then upper bound, then checks between the cells if they are covered.
	LOWER_UPPER_BETWEEN_SAMPLING_WITH_BOUNDS // First checks lower bound and then upper bound, then checks between the cells if they are covered, but respects closed interval bounds.
};

enum IsSampleOutsideAlgorithm {
	DEFAULT, // Check if its outside of each cell individually
	BOUND_FOCUS // Check if its outside of each cell individually, but with respect to closed bounds
};

inline std::string get_name(SamplingAlgorithm samplingAlgorithm) {
	switch (samplingAlgorithm) {
	case SamplingAlgorithm::LOWER_UPPER_BETWEEN_SAMPLING:
		return "LOWER_UPPER_BETWEEN_SAMPLING";
	case SamplingAlgorithm::LOWER_UPPER_BETWEEN_SAMPLING_WITH_BOUNDS:
		return "LOWER_UPPER_BETWEEN_SAMPLING_WITH_BOUNDS";
	default:
		return "UNKNOWN";
	}
}

inline std::string get_name(IsSampleOutsideAlgorithm samplingAlgorithm) {
	switch (samplingAlgorithm) {
	case IsSampleOutsideAlgorithm::DEFAULT:
		return "DEFAULT";
	case IsSampleOutsideAlgorithm::BOUND_FOCUS:
		return "BOUND_FOCUS";
	default:
		return "UNKNOWN";
	}
}

/*
 * @brief Sampling algorithm checking if a the given set of derivations ref is fully covering
 * @param derivations Vector of sampled derivations, assumed as being sorted by lower bounds
 * @param sample, RAN which is set if the vector of derivations is not covering
 * @note redundancies of the first kind are not removed
 * @return 0 if the vector of derivations is covering, 1 if the vector of derivations is not covering
 */
template<SamplingAlgorithm S>
struct sampling {
	template<typename T>
	static size_t sample_outside(cadcells::RAN& sample, const std::set<cadcells::datastructures::SampledDerivationRef<T>, SampledDerivationRefCompare>& derivations);
};

/*
 * @brief Algorithm to check if the given sample is outside of the given derivations/cells
 * @param sample, RAN which is to be checked
 * @param Set of derivations sorted by lower bound
 * @Note In the given set of derivations, the redundancies of the first kind are not removed
 * @return True if the sample is outside of the given set of derivations, false otherwise
 */
template<IsSampleOutsideAlgorithm S>
struct is_sample_outside {
	template<typename T>
	static bool is_outside(const cadcells::RAN& sample, const std::set<cadcells::datastructures::SampledDerivationRef<T>, SampledDerivationRefCompare>& derivations);
};

template<>
struct sampling<SamplingAlgorithm::LOWER_UPPER_BETWEEN_SAMPLING> {
	template<typename T>
	static size_t sample_outside(cadcells::RAN& sample, const std::set<cadcells::datastructures::SampledDerivationRef<T>, SampledDerivationRefCompare>& derivationsSet) {
		SMTRAT_LOG_DEBUG("smtrat.covering","Current Intervals");
		auto iter2 = derivationsSet.begin();
		while (iter2 != derivationsSet.end()) {
			SMTRAT_LOG_DEBUG("smtrat.covering","-- " << (*iter2)->cell());
			iter2++;
		}

		// remove redundancies of the first kind
		// the derivations are already sorted by lower bound
		std::vector<cadcells::datastructures::SampledDerivationRef<T>> derivationsVector;
		auto iter = derivationsSet.begin();
		while (iter != derivationsSet.end()) {
			derivationsVector.push_back(*iter);
			auto& last_cell = (*iter)->cell();
			iter++;
			while (iter != derivationsSet.end() && !cadcells::datastructures::upper_lt_upper(last_cell, (*iter)->cell()))
				iter++;
		}

		SMTRAT_LOG_DEBUG("smtrat.covering","Simplified Intervals");
		for (size_t i = 0; i < derivationsVector.size(); i++) {
			SMTRAT_LOG_DEBUG("smtrat.covering","-- " << derivationsVector[i]->cell());
		}

		if (derivationsVector.empty()) {
			// There are no cells, just take trivially 0
			sample = cadcells::RAN(0);
			SMTRAT_LOG_DEBUG("smtrat.covering","- Current Sample " << sample << " because set is empty.");
			//SMTRAT_STATISTICS_CALL(getStatistics().calledSample());
			return 0;
		}

		if (!derivationsVector.front()->cell().lower_unbounded()) {
			// Lower bound is finite, just take a sufficiently large negative number
			sample = carl::sample_below(derivationsVector.front()->cell().lower()->first);
			SMTRAT_LOG_DEBUG("smtrat.covering","- Current Sample " << sample << " because lowest interval not -oo.");
			//SMTRAT_STATISTICS_CALL(getStatistics().calledSample());
			return 0;
		}

		if (!derivationsVector.back()->cell().upper_unbounded()) {
			// Upper bound is finite, just take a sufficiently large positive number
			sample = carl::sample_above(derivationsVector.back()->cell().upper()->first);
			SMTRAT_LOG_DEBUG("smtrat.covering","- Current Sample " << sample << " because lowest interval not oo.");
			//SMTRAT_STATISTICS_CALL(getStatistics().calledSample());
			return 0;
		}

		// Search for adjacent disjoint cells and sample between
		for (size_t i = 0; i + 1 < derivationsVector.size(); i++) {
			// We know that the cells are ordered by lower bound - so for checking disjointness the following suffices
			if (!derivationsVector[i]->cell().upper_unbounded() && !derivationsVector[i + 1]->cell().lower_unbounded() && derivationsVector[i]->cell().upper()->first < derivationsVector[i + 1]->cell().lower()->first) {
				sample = carl::sample_between(derivationsVector[i]->cell().upper()->first, derivationsVector[i + 1]->cell().lower()->first);
				//SMTRAT_STATISTICS_CALL(getStatistics().calledSample());
				SMTRAT_LOG_DEBUG("smtrat.covering","- Current Sample " << sample << " because b < c and b][c or b)[c or b](c or b)(c. b=" << derivationsVector[i]->cell().upper()->first << " and c=" << derivationsVector[i + 1]->cell().lower()->first << ".");
				return 0;

				// The check above does not care for open bounds
				// i.e if we have (x, y), (y, z) we can still choose y as a sample point
			} else if (derivationsVector[i]->cell().is_sector() && derivationsVector[i + 1]->cell().is_sector() && derivationsVector[i]->cell().upper()->first == derivationsVector[i + 1]->cell().lower()->first) {
				sample = derivationsVector[i]->cell().upper()->first;
				SMTRAT_LOG_DEBUG("smtrat.covering","- Current Sample " << sample << " because b)(b. b=" << derivationsVector[i]->cell().upper()->first << ".");
				//SMTRAT_STATISTICS_CALL(getStatistics().calledBoundSample());
				return 0;
			}
		}

		// The cells cover the number line -> There is no sample to be found
		SMTRAT_LOG_DEBUG("smtrat.covering","- Current Sample not found, because full covering");
		return 1;
	}
};

template<>
struct is_sample_outside<IsSampleOutsideAlgorithm::DEFAULT> {
	template<typename T>
	static bool is_outside(const cadcells::RAN& sample, const std::set<cadcells::datastructures::SampledDerivationRef<T>, SampledDerivationRefCompare>& derivations) {

		SMTRAT_LOG_DEBUG("smtrat.covering","Checking if " << sample << " is outside of " << derivations);

		if(derivations.empty()) {
			SMTRAT_LOG_DEBUG("smtrat.covering","No cells, so " << sample << " is outside");
			return true;
		}

		for (const auto& deriv : derivations) {
			auto& cell = deriv->cell();
			SMTRAT_LOG_DEBUG("smtrat.covering","Checking if " << sample << " is outside of " << cell);
			SMTRAT_LOG_DEBUG("smtrat.covering", " Lower unbounded "<< cell.lower_unbounded() << " Upper unbounded " << cell.upper_unbounded());

			//When one bound is infty, we must have a sector
			if (cell.lower_unbounded() && cell.upper_unbounded()) {
				// (-infty, infty)
				return false;
			} else if (!cell.lower_unbounded() && cell.upper_unbounded()) {
				// (a, infty)
				if(sample > cell.lower()->first){
					return false ;
				}
			} else if (cell.lower_unbounded() && !cell.upper_unbounded()) {
				// (-infty, a)
				if(sample < cell.upper()->first){
					return false ;
				}
			} else {
				// both cells bounds are not infty
				if (cell.is_section()) {
					// [a,b]
					// Non-strict bounds
					if (cell.lower()->first <= sample && sample <= cell.upper()->first) {
						return false;
					}
				} else {
					// Strict bounds
					// (a,b)
					if (cell.lower()->first < sample && sample < cell.upper()->first) {
						return false;
					}
				}
			}
		}
		return true ;
	}
};

template<>
struct sampling<SamplingAlgorithm::LOWER_UPPER_BETWEEN_SAMPLING_WITH_BOUNDS> {
	template<typename T>
	static size_t sample_outside(cadcells::RAN& sample, const std::set<cadcells::datastructures::SampledDerivationRef<T>, SampledDerivationRefCompare>& derivationsSet) {
		SMTRAT_LOG_DEBUG("smtrat.covering","Current Intervals");
		auto iter2 = derivationsSet.begin();
		while (iter2 != derivationsSet.end()) {
			SMTRAT_LOG_DEBUG("smtrat.covering","-- " << (*iter2)->cell() << " " << (*iter2)->cell().get_strictness_of_ancestor_intervals());
			iter2++;
		}

		// remove redundancies of the first kind
		// the derivations are already sorted by lower bound
		std::vector<cadcells::datastructures::SampledDerivationRef<T>> derivationsVector;
		auto iter = derivationsSet.begin();
		while (iter != derivationsSet.end()) {
			derivationsVector.push_back(*iter);
			auto& last_cell = (*iter)->cell();
			iter++;
			while (iter != derivationsSet.end() && !cadcells::datastructures::upper_lt_upper(last_cell, (*iter)->cell()))
				iter++;
		}

		SMTRAT_LOG_DEBUG("smtrat.covering","Simplified Intervals");
		for (size_t i = 0; i < derivationsVector.size(); i++) {
			SMTRAT_LOG_DEBUG("smtrat.covering","-- " << derivationsVector[i]->cell());
		}

		if (derivationsVector.empty()) {
			// There are no cells, just take trivially 0
			sample = cadcells::RAN(0);
			SMTRAT_STATISTICS_CALL(getStatistics().calledSample());
			SMTRAT_LOG_DEBUG("smtrat.covering","- Current Sample " << sample << " because set is empty.");
			return 0;
		}

		if (!derivationsVector.front()->cell().lower_unbounded()) {
			// Lower bound is finite, just take a sufficiently large negative number
			sample = carl::sample_below(derivationsVector.front()->cell().lower()->first);
			SMTRAT_LOG_DEBUG("smtrat.covering","- Current Sample " << sample << " because lowest interval not -oo.");
			SMTRAT_STATISTICS_CALL(getStatistics().calledSample());
			return 0;
		}

		if (!derivationsVector.back()->cell().upper_unbounded()) {
			// Upper bound is finite, just take a sufficiently large positive number
			sample = carl::sample_above(derivationsVector.back()->cell().upper()->first);
			SMTRAT_LOG_DEBUG("smtrat.covering","- Current Sample " << sample << " because highest interval not oo.");
			SMTRAT_STATISTICS_CALL(getStatistics().calledSample());
			return 0;
		}

		// Search for adjacent disjoint cells and sample between
		for (size_t i = 0; i + 1 < derivationsVector.size(); i++) {
			// We know that the cells are ordered by lower bound - so for checking disjointness the following suffices
			if (!derivationsVector[i]->cell().upper_unbounded() && !derivationsVector[i + 1]->cell().lower_unbounded() && derivationsVector[i]->cell().upper()->first < derivationsVector[i + 1]->cell().lower()->first) {
				sample = carl::sample_between(derivationsVector[i]->cell().upper()->first, derivationsVector[i + 1]->cell().lower()->first);
				SMTRAT_LOG_DEBUG("smtrat.covering","- Current Sample " << sample << " because b < c and b][c or b)(c. b=" << derivationsVector[i]->cell().upper()->first << " and c=" << derivationsVector[i + 1]->cell().lower()->first << ".");
				SMTRAT_STATISTICS_CALL(getStatistics().calledSample());
				return 0;

				// The check above does not care for open bounds
				// i.e if we have (x, y), (y, z) we can still choose y as a sample point
			} else if (!derivationsVector[i]->cell().upper_unbounded() && !derivationsVector[i + 1]->cell().lower_unbounded() && derivationsVector[i]->cell().upper()->first == derivationsVector[i + 1]->cell().lower()->first){
				if(derivationsVector[i]->cell().upper_inclusive() && derivationsVector[i + 1]->cell().lower_inclusive()) {
					// We have the situation   ;a][a;
					continue;
				} else if(derivationsVector[i]->cell().upper_inclusive() && !derivationsVector[i + 1]->cell().lower_inclusive()) {
					// We have the situation   ;a](a;
					continue;
				} else if(!derivationsVector[i]->cell().upper_inclusive() && derivationsVector[i + 1]->cell().lower_inclusive()) {
					// We have the situation   ;a)[a;
					continue;
				} else {
					// We have the situation   ;a)(a; --> sampling needed
					sample = derivationsVector[i]->cell().upper()->first;
					SMTRAT_LOG_DEBUG("smtrat.covering","- Current Sample " << sample << " because b)(b. b=" << derivationsVector[i]->cell().upper()->first << ".");
					SMTRAT_STATISTICS_CALL(getStatistics().calledBoundSample());
					return 0;
				}
			}
		}

		// The cells cover the number line -> There is no sample to be found
		SMTRAT_LOG_DEBUG("smtrat.covering","- Current Sample not found, because full covering");
		return 1;
	}
};

template<>
struct is_sample_outside<IsSampleOutsideAlgorithm::BOUND_FOCUS> {
	template<typename T>
	static bool is_outside(const cadcells::RAN& sample, const std::set<cadcells::datastructures::SampledDerivationRef<T>, SampledDerivationRefCompare>& derivations) {
		SMTRAT_LOG_DEBUG("smtrat.covering","Checking if " << sample << " is outside of " << derivations);

		if(derivations.empty()) {
			SMTRAT_LOG_DEBUG("smtrat.covering","No cells, so " << sample << " is outside");
			return true;
		}

		// Sample refered to as s
		for (const auto& deriv : derivations) {
			auto& cell = deriv->cell();
			SMTRAT_LOG_DEBUG("smtrat.covering","Checking if " << sample << " is outside of " << cell);
			SMTRAT_LOG_DEBUG("smtrat.covering", " Lower unbounded "<< cell.lower_unbounded() << " Upper unbounded " << cell.upper_unbounded());

			//When one bound is infty, we must have a sector
			if (cell.lower_unbounded() && cell.upper_unbounded()) {
				// (-infty, infty)
				return false;
			} else if (!cell.lower_unbounded() && cell.upper_unbounded()) {
				if(sample > cell.lower()->first){
					// (a, infty) or [a, infty) but sample s > a
					return false ;
				} else if(sample == cell.lower()->first && cell.lower_inclusive()) {
					// [a, infty) and a = s
					return false;
				}
			} else if (cell.lower_unbounded() && !cell.upper_unbounded()) {
				if(sample < cell.upper()->first){
					// (-infty, a) or (-infty, a] but sample s < a
					return false ;
				} else if(sample == cell.upper()->first && cell.upper_inclusive()) {
					// (-infty, a] and a = s
					return false;
				}
			} else {
				// both cells bounds are not infty
				if(cell.lower()->first < sample && sample < cell.upper()->first) {
					// a < s < b
					return false;
				} else if(cell.lower_inclusive() && sample == cell.lower()->first) {
					// [a,b) or [a,b] and a = s
					return false;
				} else if(cell.upper_inclusive() && sample == cell.upper()->first) {
					// (a,b] or [a,b] and b = s
					return false;
				}
			}
		}
		return true ;
	}
};
}; // namespace smtrat
