#pragma once

#include <carl/util/Bitset.h>
#include <smtrat-common/smtrat-common.h>

#include <iostream>
#include <map>

namespace smtrat {
namespace mcsat {
namespace arithmetic {

	
/**
 * Semantics:
 * The space is divided into a number of intervals: (-oo,a)[a,a](a,b)[b,b](b,oo)
 * A bit is set if the constraints refutes the corresponding interval
 */
class Covering {
	friend std::ostream& operator<<(std::ostream& os, const Covering& ri);
private:
	std::map<FormulaT, carl::Bitset> mData;
	carl::Bitset mOkay;
public:
	Covering(std::size_t intervals) {
		mOkay.resize(intervals, true);
	}
	void add(const FormulaT& c, const carl::Bitset& b) {
		mData.emplace(c, b);
		mOkay -= b;
	}
	bool conflicts() const {
		return mOkay.none();
	}
	std::size_t satisfyingInterval() const {
		return mOkay.find_first();
	}
	const auto& satisfyingSamples() const {
		return mOkay;
	}
	void buildConflictingCore(std::vector<FormulaT>& core) const {
		std::map<FormulaT, carl::Bitset> data = mData;
		carl::Bitset covered;
		covered.resize(mOkay.size(), true);
		while (covered.any()) {
			auto maxit = data.begin();
			for (auto it = data.begin(); it != data.end(); it++) {
				if (maxit->second.count() < it->second.count()) maxit = it;
			}
			core.push_back(maxit->first);
			covered -= maxit->second;
			data.erase(maxit);
			for (auto& d: data) {
				d.second &= covered;
			}
		}
	}
};
inline std::ostream& operator<<(std::ostream& os, const Covering& ri) {
	os << "Covering: " << ri.mOkay << std::endl;
	for (const auto& d: ri.mData) {
		os << "\t" << d.first << " -> " << d.second << std::endl;
	}
	return os;
}

}
}
}
