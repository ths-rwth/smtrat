#include "triangular_ordering.h"

#include <algorithm>
#include <numeric>

namespace smtrat::cad::variable_ordering {

template<typename T>
class VariableMap {
private:
	std::vector<T> mData;
public:
	T operator[](carl::Variable v) const {
		assert(v != carl::Variable::NO_VARIABLE);
		if (mData.size() <= v.id() - 1) return 0;
		return mData[v.id() - 1];
	}
	T& operator[](carl::Variable v) {
		assert(v != carl::Variable::NO_VARIABLE);
		if (mData.size() <= v.id() - 1) mData.resize(v.id());
		return mData[v.id() - 1];
	}
};

struct triangular_data {
	VariableMap<std::size_t> max_deg;
	VariableMap<std::size_t> max_tdeg;
	VariableMap<std::size_t> sum_deg;
	
	bool operator()(carl::Variable lhs, carl::Variable rhs) const {
		SMTRAT_LOG_TRACE("smtrat.cad.variableordering", "Comparing maxdeg " << lhs << " < " << rhs << "? " << max_deg[lhs] << " > " << max_deg[rhs]);
		if (max_deg[lhs] != max_deg[rhs]) return max_deg[lhs] < max_deg[rhs];
		SMTRAT_LOG_TRACE("smtrat.cad.variableordering", "Comparing maxtdeg " << lhs << " < " << rhs << "? " << max_tdeg[lhs] << " > " << max_tdeg[rhs]);
		if (max_tdeg[lhs] != max_tdeg[rhs]) return max_tdeg[lhs] < max_tdeg[rhs];
		SMTRAT_LOG_TRACE("smtrat.cad.variableordering", "Comparing degsum " << lhs << " < " << rhs << "? " << sum_deg[lhs] << " > " << sum_deg[rhs]);
		if (sum_deg[lhs] != sum_deg[rhs]) return sum_deg[lhs] < sum_deg[rhs];
		return false;
	}
};

std::vector<carl::Variable> triangular_ordering(const std::vector<Poly>& polys) {
	SMTRAT_LOG_DEBUG("smtrat.cad.variableordering", "Building order based on " << polys);
	carl::carlVariables vars;
	triangular_data data;
	std::vector<VariableMap<std::size_t>> maxdeg;
	maxdeg.resize(polys.size());
	for (std::size_t i = 0; i < polys.size(); ++i) {
		carl::variables(polys[i], vars);
		for (auto var: carl::variables(polys[i])) { 
			maxdeg[i][var] = polys[i].degree(var);
			data.max_deg[var] = std::max(data.max_deg[var], maxdeg[i][var]);
			data.max_tdeg[var] = std::max(data.max_tdeg[var], polys[i].lcoeff(var).total_degree());
		}
	}
	for (auto var: vars) {
		data.sum_deg[var] = std::accumulate(maxdeg.begin(), maxdeg.end(), 0ul, [var](std::size_t i, const auto& m) { return i + m[var]; });
	}
	SMTRAT_LOG_DEBUG("smtrat.cad.variableordering", "Collected variables: " << vars);
	std::vector<carl::Variable> res(vars.as_vector());
	std::sort(res.begin(), res.end(), data);
	SMTRAT_LOG_DEBUG("smtrat.cad.variableordering", "Sorted: " << res);
	return res;
}

}