#pragma once

#include "../../../Common.h"

#include <carl/core/Variable.h>
#include <carl/util/Bitset.h>

#include <algorithm>
#include <map>
#include <vector>

namespace smtrat {
namespace mcsat {

namespace detail {

struct VariableIDs {
	std::map<carl::Variable, std::size_t> mIDs;
	std::size_t operator[](carl::Variable v) {
		auto it = mIDs.find(v);
		if (it == mIDs.end()) {
			it = mIDs.emplace(v, mIDs.size()).first;
		}
		return it->second;
	}
	std::size_t operator[](carl::Variable v) const {
		assert(mIDs.find(v) != mIDs.end());
		return mIDs.find(v)->second;
	}
};

inline carl::Bitset variablesOf(const FormulaT& c, VariableIDs& vids) {
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
std::vector<carl::Variable> constructVariableOrdering(const Constraints& c) {
	detail::VariableIDs vids;
	std::vector<carl::Bitset> constraints;
	for (int i = 0; i < c.size(); ++i) {
		if (c[i].first == nullptr) continue;
		constraints.emplace_back(detail::variablesOf(c[i].first->reabstraction, vids));
	}
	
	std::vector<carl::Variable> order;
	while (!constraints.empty()) {
		order.emplace_back(findMax(constraints, vids));
		purgeVariable(constraints, order.back(), vids);
	}
	return order;
}

}
}
