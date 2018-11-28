#pragma once

#include "helper.h"

#include <carl/core/Variable.h>
#include <carl/util/Bitset.h>
#include <smtrat-common/smtrat-common.h>

#include <algorithm>
#include <map>
#include <vector>

namespace smtrat {
namespace mcsat {
namespace variableordering {

namespace detail {
inline carl::Bitset variablesOf(const ConstraintT& c, VariableIDs& vids) {
	carl::Bitset res;
	for (auto v: c.variables()) {
		res.set(vids[v]);
	}
	return res;
}

inline long countUnivariates(const std::vector<carl::Bitset>& constraints, std::size_t id) {
	return std::count(constraints.begin(), constraints.end(), carl::Bitset({id}));
}
inline bool stillOccurs(const std::vector<carl::Bitset>& constraints, std::size_t id) {
	return std::find_if(constraints.begin(), constraints.end(), [id](const auto& b){ return b.test(id); }) != constraints.end();
}
inline carl::Variable findMax(const std::vector<carl::Bitset>& constraints, const VariableIDs& vids) {
	carl::Variable maxVar = carl::Variable::NO_VARIABLE;
	carl::Variable possible = carl::Variable::NO_VARIABLE;
	long maxCnt = 0;
	for (const auto& v: vids.mIDs) {
		auto cnt = detail::countUnivariates(constraints, v.second);
		if (cnt > maxCnt) {
			maxVar = v.first;
			maxCnt = cnt;
		}
		if (possible == carl::Variable::NO_VARIABLE) {
			if (stillOccurs(constraints, v.second)) {
				possible = v.first;
			}
		}
	}
	if (maxVar != carl::Variable::NO_VARIABLE) return maxVar;
	return possible;
}

inline void purgeVariable(std::vector<carl::Bitset>& constraints, carl::Variable v, const VariableIDs& vids) {
	std::size_t id = vids[v];
	for (auto it = constraints.begin(); it != constraints.end(); ) {
		auto& bitset = *it;
		bitset.reset(id);
		if (bitset.none()) {
			it = constraints.erase(it);
		} else {
			++it;
		}
	}
}

}

template<typename Constraints>
std::vector<carl::Variable> greedy_max_univariate(const Constraints& c) {
	VariableIDs vids;
	std::vector<carl::Bitset> constraints;
	for (const auto& cons: c) {
		constraints.emplace_back(detail::variablesOf(cons, vids));
		SMTRAT_LOG_DEBUG("smtrat.mcsat", "Constraint " << cons << " -> " << constraints.back());
	}
	SMTRAT_LOG_DEBUG("smtrat.mcsat", "Collected variables " << vids);
	
	std::vector<carl::Variable> res;
	while (!constraints.empty()) {
		res.emplace_back(detail::findMax(constraints, vids));
		detail::purgeVariable(constraints, res.back(), vids);
	}
	SMTRAT_LOG_DEBUG("smtrat.mcsat", "Calculated variable ordering " << res);
	return res;
	
}

}
}
}
