#pragma once

namespace smtrat::covering_ng {


enum class SamplingAlgorithm {
    /// First checks lower bound and then upper bound, then checks between the cells if they are covered.
    LOWER_UPPER_BETWEEN_SAMPLING 
};

/*
 * @brief Sampling algorithm checking if a the given set of derivations ref is fully covering
 * @param derivations Vector of sampled derivations, assumed as being sorted by lower bounds
 * @note redundancies of the first kind are not removed
 * @return std::nullopt if the vector of derivations is covering, a real algebraic number if the vector of derivations is not covering
 */
template<SamplingAlgorithm S>
struct sampling {
    template<cadcells::operators::op op>
    static std::optional<cadcells::RAN> sample_outside(const IntervalSet<op>& derivations, const formula::FormulaEvaluation& f);
};

template<>
struct sampling<SamplingAlgorithm::LOWER_UPPER_BETWEEN_SAMPLING> {
    template<cadcells::operators::op op>
    static std::optional<cadcells::RAN> sample_outside(const IntervalSet<op>& intervals, const formula::FormulaEvaluation&) {
        // remove redundancies of the first kind
        // the derivations are already sorted by lower bound
        std::vector<Interval<op>> derivs;
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

}; // namespace smtrat
