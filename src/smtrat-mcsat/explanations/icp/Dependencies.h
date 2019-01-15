#pragma once

#include <carl/util/Bitset.h>
#include <smtrat-common/smtrat-common.h>

namespace smtrat {
namespace mcsat {
namespace icp {

class Dependencies {
private:
	std::vector<FormulaT> mConstraints;
	std::map<FormulaT,std::size_t> mConstraintIDs;
	std::map<carl::Variable,carl::Bitset> mData;

	std::size_t get_constraint_id(const FormulaT& c) {
		auto it = mConstraintIDs.find(c);
		if (it == mConstraintIDs.end()) {
			it = mConstraintIDs.emplace(c, mConstraintIDs.size()).first;
			mConstraints.emplace_back(c);
		}
		return it->second;
	}
public:
	template<typename Contractor>
	void add(const Contractor& c) {
		add(c.var(), c.origin(), c.dependees());
	}

	void add(carl::Variable v, const FormulaT& c, const std::vector<carl::Variable>& used) {
		auto& bs = mData[v];
		bs.set(get_constraint_id(c));
		SMTRAT_LOG_DEBUG("smtrat.mcsat.icp", "Added " << c << " to " << v << " -> " << bs);
		for (auto used_var: used) {
			bs = bs | mData[used_var];
			SMTRAT_LOG_DEBUG("smtrat.mcsat.icp", "Added " << mData[used_var] << " from " << used_var << " to " << v << " -> " << bs);
		}
	}

	std::vector<FormulaT> get(carl::Variable v, bool negate = true) const {
		std::vector<FormulaT> res;
		auto it = mData.find(v);
		assert(it != mData.end());
		for (std::size_t i: it->second) {
			res.emplace_back(negate ? !mConstraints[i] : mConstraints[i]);
		}
		return res;
	}
};

}
}
}