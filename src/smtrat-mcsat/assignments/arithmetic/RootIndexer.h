#pragma once

#include <smtrat-common/smtrat-common.h>

#include <algorithm>
#include <list>
#include <map>
#include <vector>

namespace smtrat {
namespace mcsat {
namespace arithmetic {

template<typename RANT>
class RootIndexer {
private:
	std::vector<RANT> mRoots;
	std::map<RANT, std::size_t> mMap;
	std::vector<RANT> mSamples;
public:	
	void add(const std::vector<RANT>& list) {
		mRoots.insert(mRoots.end(), list.begin(), list.end());
	}
	void process() {
		std::sort(mRoots.begin(), mRoots.end());
		mRoots.erase(std::unique(mRoots.begin(), mRoots.end()), mRoots.end());
		SMTRAT_LOG_DEBUG("smtrat.mcsat.rootindexer", "Roots: " << mRoots);
		for (std::size_t i = 0; i < mRoots.size(); i++) {
			mMap.emplace(mRoots[i], i);
		}
		mSamples.reserve(2 * mRoots.size() + 1);
		for (std::size_t n = 0; n < mRoots.size(); n++) {
			if (n == 0) mSamples.emplace_back(carl::sample_below(mRoots.front()));
			else mSamples.emplace_back(carl::sample_between(mRoots[n-1], mRoots[n]));
			mSamples.emplace_back(mRoots[n]);
		}
		if (mRoots.empty()) mSamples.emplace_back(RANT(0));
		else mSamples.emplace_back(carl::sample_above(mRoots.back()));
		SMTRAT_LOG_DEBUG("smtrat.mcsat.rootindexer", "Samples: " << mSamples);
	}
	std::size_t size() const {
		return mRoots.size();
	}
	std::size_t operator[](const RANT& ran) const {
		auto it = mMap.find(ran);
		assert(it != mMap.end());
		return it->second;
	}
	const RANT& operator[](std::size_t n) const {
		assert(n < mRoots.size());
		return mRoots[n];
	}
	const RANT& sampleFrom(std::size_t n) const {
		return mSamples[n];
	}
	bool is_root(std::size_t n) const {
		return (n % 2) == 1;
	}
};
template<typename RANT>
inline std::ostream& operator<<(std::ostream& os, const RootIndexer<RANT>& ri) {
	os << "Roots:" << std::endl;
	for (std::size_t i = 0; i < ri.size(); i++) {
		os << "\t" << i << ": " << ri[i] << std::endl;
	}
	os << "Samples:" << std::endl;
	for (std::size_t i = 0; i < ri.size()*2+1; i++) {
		os << "\t" << i << ": " << ri.sampleFrom(i) << std::endl;;
	}
	return os;
}


}
}
}
