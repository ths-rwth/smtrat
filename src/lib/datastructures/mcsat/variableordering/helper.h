#pragma once

#include <carl/core/Variable.h>

#include <map>
#include <vector>

namespace smtrat {
namespace mcsat {
namespace variableordering {

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
		assert(var.second < v.size());
		v[var.second] = var.first;
	}
	return os << v;
}

template<typename Constraints>
std::vector<carl::Variable> collectVariables(const Constraints& constraints) {
	std::set<carl::Variable> vars;
	for (const auto& c: constraints) {
		vars.insert(c.variables().begin(), c.variables().end());
	}
	return std::vector<carl::Variable>(vars.begin(), vars.end());
}

}
}
}
