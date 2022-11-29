/**
 * @file Sampling.h
 * @author Philip Kroll <Philip.Kroll@rwth-aachen.de>
 * Created on 2022-03-16.
 */
#pragma once

#include <smtrat-cadcells/common.h>
#include <smtrat-cadcells/datastructures/delineation.h>
#include <smtrat-cadcells/datastructures/derivation.h>
#include "Helper.h"
#include "NewCoveringStatistics.h"
#include <smtrat-common/smtrat-common.h>

namespace smtrat {

enum SamplingAlgorithm {
    LOWER_UPPER_BETWEEN_SAMPLING // First checks lower bound and then upper bound, then checks between the cells if they are covered.
};

enum IsSampleOutsideAlgorithm {
    DEFAULT // Check if its outside of each cell individually
};

inline std::string get_name(SamplingAlgorithm samplingAlgorithm) {
    switch (samplingAlgorithm) {
    case SamplingAlgorithm::LOWER_UPPER_BETWEEN_SAMPLING:
        return "LOWER_UPPER_BETWEEN_SAMPLING";
    default:
        return "UNKNOWN";
    }
}

inline std::string get_name(IsSampleOutsideAlgorithm samplingAlgorithm) {
    switch (samplingAlgorithm) {
    case IsSampleOutsideAlgorithm::DEFAULT:
        return "DEFAULT";
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

        if (derivationsVector.empty()) {
            // There are no cells, just take trivially 0
            sample = cadcells::RAN(0);
            return 0;
        }

        if (!derivationsVector.front()->cell().lower_unbounded()) {
            // Lower bound is finite, just take a sufficiently large negative number
            sample = carl::sample_below(derivationsVector.front()->cell().lower()->first);
            return 0;
        }

        if (!derivationsVector.back()->cell().upper_unbounded()) {
            // Upper bound is finite, just take a sufficiently large positive number
            sample = carl::sample_above(derivationsVector.back()->cell().upper()->first);
            return 0;
        }

        // Search for adjacent disjoint cells and sample between
        for (size_t i = 0; i + 1 < derivationsVector.size(); i++) {
            // We know that the cells are ordered by lower bound - so for checking disjointness the following suffices
            if (!derivationsVector[i]->cell().upper_unbounded() && !derivationsVector[i + 1]->cell().lower_unbounded() && derivationsVector[i]->cell().upper()->first < derivationsVector[i + 1]->cell().lower()->first) {
                sample = carl::sample_between(derivationsVector[i]->cell().upper()->first, derivationsVector[i + 1]->cell().lower()->first);
                return 0;

                // The check above does not care for open bounds
                // i.e if we have (x, y), (y, z) we can still choose y as a sample point
            } else if (derivationsVector[i]->cell().is_sector() && derivationsVector[i + 1]->cell().is_sector() && derivationsVector[i]->cell().upper()->first == derivationsVector[i + 1]->cell().lower()->first) {
                sample = derivationsVector[i]->cell().upper()->first;
                return 0;
            }
        }

        // The cells cover the number line -> There is no sample to be found
        return 1;
    }
};

template<>
struct is_sample_outside<IsSampleOutsideAlgorithm::DEFAULT> {
    template<typename T>
    static bool is_outside(const cadcells::RAN& sample, const std::set<cadcells::datastructures::SampledDerivationRef<T>, SampledDerivationRefCompare>& derivations) {

        SMTRAT_LOG_DEBUG("smtrat.covering", "Checking if " << sample << " is outside of " << derivations);

        if (derivations.empty()) {
            SMTRAT_LOG_DEBUG("smtrat.covering", "No cells, so " << sample << " is outside");
            return true;
        }

        for (const auto& deriv : derivations) {
            auto& cell = deriv->cell();
            SMTRAT_LOG_DEBUG("smtrat.covering", "Checking if " << sample << " is outside of " << cell);
            SMTRAT_LOG_DEBUG("smtrat.covering", " Lower unbounded " << cell.lower_unbounded() << " Upper unbounded " << cell.upper_unbounded());

            // When one bound is infty, we must have a sector
            if (cell.lower_unbounded() && cell.upper_unbounded()) {
                // (-infty, infty)
                return false;
            } else if (!cell.lower_unbounded() && cell.upper_unbounded()) {
                // (a, infty)
                if (sample > cell.lower()->first) {
                    return false;
                }
            } else if (cell.lower_unbounded() && !cell.upper_unbounded()) {
                // (-infty, a)
                if (sample < cell.upper()->first) {
                    return false;
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
        return true;
    }
};

}; // namespace smtrat
