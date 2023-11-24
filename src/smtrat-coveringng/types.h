#pragma once

#include <smtrat-common/smtrat-common.h>
#include <smtrat-cadcells/common.h>
#include <smtrat-cadcells/datastructures/delineation.h>
#include <smtrat-cadcells/datastructures/derivation.h>
#include <smtrat-cadcells/datastructures/polynomials.h>
#include <smtrat-cadcells/datastructures/projections.h>
#include <smtrat-cadcells/operators/operator_mccallum.h>
#include <smtrat-cadcells/operators/operator_mccallum_complete.h>
#include <smtrat-cadcells/representation/heuristics.h>

namespace smtrat::covering_ng {

template<cadcells::operators::op op>
using Interval = cadcells::datastructures::SampledDerivationRef<typename cadcells::operators::PropertiesSet<op>::type>;
/**
 * Sorts interval by their lower bounds. 
 */
template<cadcells::operators::op op>
struct IntervalCompare {
	inline constexpr bool operator()(const Interval<op>& a, const Interval<op>& b) const {
		auto cell_a = a->cell();
		auto cell_b = b->cell();
		return cadcells::datastructures::lower_lt_lower(cell_a, cell_b) || (cadcells::datastructures::lower_eq_lower(cell_a, cell_b) && cadcells::datastructures::upper_lt_upper(cell_b, cell_a));
	}
};
template<cadcells::operators::op op>
using IntervalSet = std::set<Interval<op>, IntervalCompare<op>>;

template<cadcells::operators::op op>
struct CoveringResult {
    enum Status { SAT, UNSAT, FAILED_PROJECTION, FAILED };
    struct NONE{};

    Status status;
    std::variant<std::vector<Interval<op>>, cadcells::Assignment, NONE> content;
    
    CoveringResult() : status(FAILED), content(NONE {}) {}
    CoveringResult(Status s) : status(s), content(NONE {}) {}
    CoveringResult(std::vector<Interval<op>>& c) : status(UNSAT), content(c) {}
    CoveringResult(const cadcells::Assignment& c) : status(SAT), content(c) {}

    bool is_failed() {
        return status == FAILED_PROJECTION || status == FAILED;
    }
    bool is_failed_projection() {
        return status == FAILED_PROJECTION;
    }
    bool is_sat() const {
        return status == SAT;
    }
    bool is_unsat() const {
        return status == UNSAT;
    }
    const auto& sample() const {
        return std::get<cadcells::Assignment>(content);
    }
    const auto& intervals() const {
        return std::get<std::vector<Interval<op>>>(content);
    }
};

}