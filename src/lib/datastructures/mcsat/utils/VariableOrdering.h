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
inline std::ostream& operator<<(std::ostream& os, const VariableIDs& vids) {
	std::vector<carl::Variable> v(vids.mIDs.size());
	for (const auto& var: vids.mIDs) {
		assert(var.second >= 0 && var.second < v.size());
		v[var.second] = var.first;
	}
	return os << v;
}

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

class VariableOrdering {
	bool mInitialized = false;
	std::vector<carl::Variable> mVariables;
public:
	bool initialized() const {
		return mInitialized;
	}
	template<typename Constraints>
	void update(const Constraints& c) {
		detail::VariableIDs vids;
		std::vector<carl::Bitset> constraints;
		for (int i = 0; i < c.size(); ++i) {
			if (c[i].first == nullptr) continue;
			constraints.emplace_back(detail::variablesOf(c[i].first->reabstraction, vids));
			SMTRAT_LOG_DEBUG("smtrat.mcsat", "Constraint " << c[i].first->reabstraction << " -> " << constraints.back());
		}
		SMTRAT_LOG_DEBUG("smtrat.mcsat", "Collected variables " << vids);
		
		mVariables.clear();
		while (!constraints.empty()) {
			mVariables.emplace_back(findMax(constraints, vids));
			purgeVariable(constraints, mVariables.back(), vids);
		}
		mInitialized = true;
		SMTRAT_LOG_DEBUG("smtrat.mcsat", "Calculated variable ordering " << mVariables);
	}
	const auto& ordering() const {
		return mVariables;
	}
};

}
}
