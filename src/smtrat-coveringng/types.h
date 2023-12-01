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
#include <carl-formula/formula/functions/PNF.h>

#include <boost/container/flat_map.hpp>

namespace smtrat::covering_ng {

template<typename PropertiesSet>
using Interval = cadcells::datastructures::SampledDerivationRef<PropertiesSet>;
/**
 * Sorts interval by their lower bounds.
 */
template<typename PropertiesSet>
struct IntervalCompare {
	inline constexpr bool operator()(const Interval<PropertiesSet>& a, const Interval<PropertiesSet>& b) const {
		const auto& cell_a = a->cell();
		const auto& cell_b = b->cell();
		return cadcells::datastructures::lower_lt_lower(cell_a, cell_b) || (cadcells::datastructures::lower_eq_lower(cell_a, cell_b) && cadcells::datastructures::upper_lt_upper(cell_b, cell_a));
	}
};
template<typename PropertiesSet>
using IntervalSet = std::set<Interval<PropertiesSet>, IntervalCompare<PropertiesSet>>;

//TODO extend this s.t. the enclosing interval can be returned in any case
template<typename PropertiesSet>
struct CoveringResult {
    enum Status { SAT, UNSAT, FAILED_PROJECTION, FAILED, PARAMETER};

    Status status;
	std::optional<std::vector<Interval<PropertiesSet>>> m_intervals;
	std::optional<cadcells::Assignment> m_sample;

	CoveringResult() : status(FAILED) {}
	explicit CoveringResult(Status s) : status(s){}
	explicit CoveringResult(std::vector<Interval<PropertiesSet>>& inter) : status(UNSAT), m_intervals(inter) {}
	explicit CoveringResult(const cadcells::Assignment& ass) : status(SAT), m_sample(ass) {}
	CoveringResult(Status s, std::vector<Interval<PropertiesSet>>& inter) : status(s), m_intervals(inter) {}
	CoveringResult(Status s, std::vector<Interval<PropertiesSet>>&& inter) : status(s), m_intervals(inter) {}
	CoveringResult(Status s, const cadcells::Assignment& ass) : status(s), m_sample(ass) {}
	CoveringResult(Status s, const cadcells::Assignment& ass, const std::vector<Interval<PropertiesSet>>& inter) : status(s), m_intervals(inter), m_sample(ass) {}


    bool is_failed() const {
        return status == FAILED_PROJECTION || status == FAILED;
    }
    bool is_failed_projection() const {
        return status == FAILED_PROJECTION;
    }
    bool is_sat() const {
        return status == SAT;
    }
    bool is_unsat() const {
        return status == UNSAT;
    }
	bool is_parameter() const {
		return  status == PARAMETER;
	}
    const auto& sample() const {
        assert(m_sample.has_value() && "Sample is not set.");
		return m_sample.value();
    }
    const auto& intervals() const {
        assert(m_intervals.has_value() && "Intervals are not set.");
		return m_intervals.value();
    }
};

template<typename PropertiesSet>
std::ostream& operator<<(std::ostream& os, const CoveringResult<PropertiesSet>& result){
	switch (result.status) {
	case CoveringResult<PropertiesSet>::SAT:
		os << "SAT" ;
		break;
	case CoveringResult<PropertiesSet>::UNSAT:
		os << "UNSAT" ;
		break;
	case CoveringResult<PropertiesSet>::FAILED:
		os << "Failed" ;
		break;
	case CoveringResult<PropertiesSet>::FAILED_PROJECTION:
		os << "Failed Projection" ;
		break;
	case CoveringResult<PropertiesSet>::PARAMETER:
		os << "Parameter" ;
		break;
	}
	return os;
}

class VariableQuantification {
private:
	boost::container::flat_map<carl::Variable, carl::Quantifier> m_var_types;

public:
	[[nodiscard]] const auto& var_types() const {
		return m_var_types;
	}

	/**
	 * Returns the type of the given variable.
	 * @param var The variable.
	 * @return The type of the variable. Returns EXISTS if the variable is not quantified.
	 **/
	[[nodiscard]] carl::Quantifier var_type(const carl::Variable& var) const{
		auto it = m_var_types.find(var);
		if (it == m_var_types.end()) {
			return carl::Quantifier::FREE;
		}
		return it->second;
	}

	bool has(const carl::Variable& var) const{
		return m_var_types.find(var) != m_var_types.end();
	}

	void set_var_type(const carl::Variable& var, carl::Quantifier type){
		m_var_types[var] = type;
	}

};

inline std::ostream& operator<<(std::ostream& os, const VariableQuantification& vq) {
	for (const auto& [var, type] : vq.var_types()) {
		os << "(" << type << " " << var << ")";
	}
	return os;
}

}