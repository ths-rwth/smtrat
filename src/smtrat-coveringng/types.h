#pragma once

#include <smtrat-common/smtrat-common.h>
#include <smtrat-cadcells/common.h>
#include <smtrat-cadcells/datastructures/delineation.h>
#include <smtrat-cadcells/datastructures/derivation.h>
#include <smtrat-cadcells/datastructures/polynomials.h>
#include <smtrat-cadcells/datastructures/projections.h>
#include <smtrat-cadcells/operators/operator_mccallum.h>
#include <smtrat-cadcells/operators/operator_mccallum_filtered.h>
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

enum class Status { SAT, UNSAT, FAILED_PROJECTION, FAILED, PARAMETER };

template<typename PropertiesSet>
struct CoveringResult {
    Status status;
	std::optional<std::vector<Interval<PropertiesSet>>> m_intervals;
	std::optional<cadcells::Assignment> m_sample;

	CoveringResult() : status(Status::FAILED) {}
	explicit CoveringResult(Status s) : status(s){}
	// explicit CoveringResult(std::vector<Interval<PropertiesSet>>& inter) : status(UNSAT), m_intervals(inter) {}
	// explicit CoveringResult(const cadcells::Assignment& ass) : status(SAT), m_sample(ass) {}
	CoveringResult(Status s, std::vector<Interval<PropertiesSet>>& inter) : status(s), m_intervals(inter) {}
	CoveringResult(Status s, std::vector<Interval<PropertiesSet>>&& inter) : status(s), m_intervals(inter) {}
	CoveringResult(Status s, const cadcells::Assignment& ass) : status(s), m_sample(ass) {}
	CoveringResult(Status s, const std::optional<cadcells::Assignment>& ass) : status(s), m_sample(ass) {}
	CoveringResult(Status s, const cadcells::Assignment& ass, const std::vector<Interval<PropertiesSet>>& inter) : status(s), m_intervals(inter), m_sample(ass) {}
	CoveringResult(Status s, const std::optional<cadcells::Assignment>& ass, const std::vector<Interval<PropertiesSet>>& inter) : status(s), m_intervals(inter), m_sample(ass) {}

    bool is_failed() const {
        return status == Status::FAILED_PROJECTION || status == Status::FAILED;
    }
	bool is_failed_projection() const {
        return status == Status::FAILED_PROJECTION;
    }
    bool is_sat() const {
        return status == Status::SAT;
    }
    bool is_unsat() const {
        return status == Status::UNSAT;
    }
	bool is_parameter() const {
		return  status == Status::PARAMETER;
	}
    const auto& sample() const {
		return m_sample;
    }
    const auto& intervals() const {
        assert(m_intervals);
		return *m_intervals;
    }
};

template<typename PropertiesSet>
std::ostream& operator<<(std::ostream& os, const CoveringResult<PropertiesSet>& result){
	switch (result.status) {
	case Status::SAT:
		os << "SAT" ;
		break;
	case Status::UNSAT:
		os << "UNSAT" ;
		break;
	case Status::FAILED:
		os << "Failed" ;
		break;
	case Status::FAILED_PROJECTION:
		os << "Failed Projection" ;
		break;
	case Status::PARAMETER:
		os << "Parameter" ;
		break;
	}
	return os;
}

struct ParameterTree {
	boost::tribool status;
	std::optional<carl::Variable> variable;
	std::optional<cadcells::datastructures::SymbolicInterval> interval;
	std::optional<cadcells::Assignment> sample;
	std::vector<ParameterTree> children;

	ParameterTree() : status(boost::indeterminate) {}
	ParameterTree(bool s) : status(s) {}
	ParameterTree(const carl::Variable& v, const cadcells::datastructures::SymbolicInterval& i, const cadcells::Assignment& s, std::vector<ParameterTree>&& c) : status(boost::indeterminate), variable(v), interval(i), sample(s), children(std::move(c)) {
		assert(!children.empty());
		status = children.begin()->status;
		for (const auto& child : children) {
			if (child.status != status) {
				status = boost::indeterminate; 
				break;
			}
		}
		if (!boost::indeterminate(status)) {
			std::cout << "gotcha" << std::endl;
			children.clear();
		}
	}
	ParameterTree(std::vector<ParameterTree>&& c) : status(boost::indeterminate), children(std::move(c)) {
		assert(!children.empty());
		status = children.begin()->status;
		for (const auto& child : children) {
			if (child.status != status) {
				status = boost::indeterminate; 
				break;
			}
		}
		if (!boost::indeterminate(status)) {
			children.clear();
		}
	}
	ParameterTree(boost::tribool st, const carl::Variable& v, const cadcells::datastructures::SymbolicInterval& i, const cadcells::Assignment& s) : status(st), variable(v), interval(i), sample(s) {
		assert(!boost::indeterminate(st));
	}
};
static std::ostream& operator<<(std::ostream& os, const ParameterTree& tree){
	os << tree.status;
	if (tree.variable) {
		os << " " << *tree.variable << " " << *tree.interval << " " << *tree.sample;
	}
	os << " (" << std::endl;
	for (const auto& child : tree.children) {
		os << child << std::endl;
	}
	os << ")";
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