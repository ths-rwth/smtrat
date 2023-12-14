#pragma once

namespace smtrat::covering_ng {


enum class SamplingAlgorithm {
    LOWER_UPPER_BETWEEN_SAMPLING, LOWER_UPPER_BETWEEN_SAMPLING_AVOID_RAN
};

/*
 * @brief Sampling algorithm checking if a the given set of derivations ref is fully covering
 * @param derivations Vector of sampled derivations, assumed as being sorted by lower bounds
 * @note redundancies of the first kind are not removed
 * @return std::nullopt if the vector of derivations is covering, a real algebraic number if the vector of derivations is not covering
 */
template<SamplingAlgorithm S>
struct sampling {
    template<typename FE, typename PropertiesSet>
    static std::optional<cadcells::RAN> sample_outside(const IntervalSet<PropertiesSet>& derivations, const FE& f);
};

/// First checks lower bound and then upper bound, then checks between the cells if they are covered.
template<>
struct sampling<SamplingAlgorithm::LOWER_UPPER_BETWEEN_SAMPLING> {
    template<typename FE, typename PropertiesSet>
    static std::optional<cadcells::RAN> sample_outside(const IntervalSet<PropertiesSet>& intervals, const FE&) {
        // remove redundancies of the first kind
        // the derivations are already sorted by lower bound
        std::vector<Interval<PropertiesSet>> derivs;
        auto iter = intervals.begin();
        while (iter != intervals.end()) {
            derivs.push_back(*iter);
            auto& last_cell = (*iter)->cell();
            iter++;
            while (iter != intervals.end() && !cadcells::datastructures::upper_lt_upper(last_cell, (*iter)->cell()))
                iter++;
        }

        if (derivs.empty()) {
            // There are no cells, just take trivially 0
            return cadcells::RAN(0);
        } else if (!derivs.front()->cell().lower_unbounded()) {
            // Lower bound is finite, just take a sufficiently large negative number
            return carl::sample_below(derivs.front()->cell().lower()->first);
        } else if (!derivs.back()->cell().upper_unbounded()) {
            // Upper bound is finite, just take a sufficiently large positive number
            return carl::sample_above(derivs.back()->cell().upper()->first);
        } else {
            // Search for adjacent disjoint cells and sample between
            for (size_t i = 0; i + 1 < derivs.size(); i++) {
                // We know that the cells are ordered by lower bound - so for checking disjointness the following suffices
                if (!derivs[i]->cell().upper_unbounded() && !derivs[i + 1]->cell().lower_unbounded() && cadcells::datastructures::upper_lt_lower(derivs[i]->cell(), derivs[i + 1]->cell())) {
                    if (derivs[i]->cell().upper()->first == derivs[i + 1]->cell().lower()->first) {
                        return derivs[i]->cell().upper()->first;
                    } else {
                        return carl::sample_between(derivs[i]->cell().upper()->first, derivs[i + 1]->cell().lower()->first);
                    }
                }
            }
            // The cells cover the number line -> There is no sample to be found
            return std::nullopt;
        }
    }
};

/// First checks lower bound and then upper bound, then checks between the cells if they are covered (defers choosing interval endpoints as much as possible).
template<>
struct sampling<SamplingAlgorithm::LOWER_UPPER_BETWEEN_SAMPLING_AVOID_RAN> {
    template<typename FE, typename PropertiesSet>
    static std::optional<cadcells::RAN> sample_outside(const IntervalSet<PropertiesSet>& intervals, const FE&) {
        std::vector<Interval<PropertiesSet>> derivs;
        auto iter = intervals.begin();
        while (iter != intervals.end()) {
            derivs.push_back(*iter);
            auto& last_cell = (*iter)->cell();
            iter++;
            while (iter != intervals.end() && !cadcells::datastructures::upper_lt_upper(last_cell, (*iter)->cell()))
                iter++;
        }

        if (derivs.empty()) {
            return cadcells::RAN(0);
        } else if (!derivs.front()->cell().lower_unbounded()) {
            return carl::sample_below(derivs.front()->cell().lower()->first);
        } else if (!derivs.back()->cell().upper_unbounded()) {
            return carl::sample_above(derivs.back()->cell().upper()->first);
        } else {
            for (size_t i = 0; i + 1 < derivs.size(); i++) {
                if (!derivs[i]->cell().upper_unbounded() && !derivs[i + 1]->cell().lower_unbounded() && cadcells::datastructures::upper_lt_lower(derivs[i]->cell(), derivs[i + 1]->cell())) {
                    if (derivs[i]->cell().upper()->first != derivs[i + 1]->cell().lower()->first) {
                        return carl::sample_between(derivs[i]->cell().upper()->first, derivs[i + 1]->cell().lower()->first);
                    }
                }
            }
            for (size_t i = 0; i + 1 < derivs.size(); i++) {
                if (!derivs[i]->cell().upper_unbounded() && !derivs[i + 1]->cell().lower_unbounded() && cadcells::datastructures::upper_lt_lower(derivs[i]->cell(), derivs[i + 1]->cell())) {
                    assert (derivs[i]->cell().upper()->first == derivs[i + 1]->cell().lower()->first);
                    return derivs[i]->cell().upper()->first;
                }
            }
            return std::nullopt;
        }
    }
};

}; // namespace smtrat
